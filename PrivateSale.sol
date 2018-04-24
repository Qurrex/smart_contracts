pragma solidity ^0.4.18;

contract SafeMath {

    function safeMul(uint256 a, uint256 b) internal pure returns (uint256 ) {
        uint256 c = a * b;
        assert(a == 0 || c / a == b);
        return c;
    }

    function safeDiv(uint256 a, uint256 b) internal pure returns (uint256 ) {
        assert(b > 0);
        uint256 c = a / b;
        assert(a == b * c + a % b);
        return c;
    }

    function safeSub(uint256 a, uint256 b) internal pure returns (uint256 ) {
        assert(b <= a);
        return a - b;
    }

    function safeAdd(uint256 a, uint256 b) internal pure returns (uint256 ) {
        uint256 c = a + b;
        assert(c >= a);
        return c;
    }
}

contract ERC20 {

    /* This is a slight change to the ERC20 base standard.
    function totalSupply() constant returns (uint256 supply);
    is replaced with:
    uint256 public totalSupply;
    This automatically creates a getter function for the totalSupply.
    This is moved to the base contract since public getter functions are not
    currently recognised as an implementation of the matching abstract
    function by the compiler.
    */
    /// total amount of tokens
    uint256 public totalSupply;

    /// @param _owner The address from which the balance will be retrieved
    /// @return The balance
    function balanceOf(address _owner) public constant returns (uint256 balance);

    /// @notice send `_value` token to `_to` from `msg.sender`
    /// @param _to The address of the recipient
    /// @param _value The amount of token to be transferred
    /// @return Whether the transfer was successful or not
    function transfer(address _to, uint256 _value) public returns (bool success);

    /// @notice send `_value` token to `_to` from `_from` on the condition it is approved by `_from`
    /// @param _from The address of the sender
    /// @param _to The address of the recipient
    /// @param _value The amount of token to be transferred
    /// @return Whether the transfer was successful or not
    function transferFrom(address _from, address _to, uint256 _value) public returns (bool success);

    /// @notice `msg.sender` approves `_spender` to spend `_value` tokens
    /// @param _spender The address of the account able to transfer the tokens
    /// @param _value The amount of tokens to be approved for transfer
    /// @return Whether the approval was successful or not
    function approve(address _spender, uint256 _value) public returns (bool success);

    /// @param _owner The address of the account owning tokens
    /// @param _spender The address of the account able to transfer the tokens
    /// @return Amount of remaining tokens allowed to spent
    function allowance(address _owner, address _spender) public constant returns (uint256 remaining);

    event Transfer(address indexed _from, address indexed _to, uint256 _value);
    event Approval(address indexed _owner, address indexed _spender, uint256 _value);
}

contract StandardToken is ERC20, SafeMath {

    mapping(address => uint256) balances;
    mapping(address => mapping(address => uint256)) allowed;

    /// @dev Returns number of tokens owned by given address.
    /// @param _owner Address of token owner.
    function balanceOf(address _owner) public view returns (uint256 balance) {
        return balances[_owner];
    }

    /// @dev Transfers sender's tokens to a given address. Returns success.
    /// @param _to Address of token receiver.
    /// @param _value Number of tokens to transfer.
    function transfer(address _to, uint256 _value) public returns (bool) {
        require(_to != address(0));
        require(_value <= balances[msg.sender]);

        balances[msg.sender] = safeSub(balances[msg.sender], _value);
        balances[_to] = safeAdd(balances[_to], _value);
        Transfer(msg.sender, _to, _value);
        return true;
    }

    /// @dev Allows allowed third party to transfer tokens from one address to another. Returns success.
    /// @param _from Address from where tokens are withdrawn.
    /// @param _to Address to where tokens are sent.
    /// @param _value Number of tokens to transfer.
    function transferFrom(address _from, address _to, uint256 _value) public returns (bool) {
        require(_to != address(0));
        require(_value <= balances[_from]);
        require(_value <= allowed[_from][msg.sender]);
        
        balances[_to] = safeAdd(balances[_to], _value);
        balances[_from] = safeSub(balances[_from], _value);
        allowed[_from][msg.sender] = safeSub(allowed[_from][msg.sender], _value);
        Transfer(_from, _to, _value);
        return true;
    }

    /// @dev Sets approved amount of tokens for spender. Returns success.
    /// @param _spender Address of allowed account.
    /// @param _value Number of approved tokens.
    function approve(address _spender, uint256 _value) public returns (bool) {
        allowed[msg.sender][_spender] = _value;
        Approval(msg.sender, _spender, _value);
        return true;
    }

    /// @dev Returns number of allowed tokens for given address.
    /// @param _owner Address of token owner.
    /// @param _spender Address of token spender.
    function allowance(address _owner, address _spender) public constant returns (uint256 remaining) {
        return allowed[_owner][_spender];
    }
}

contract Ownable {

    address public owner;
    address public pendingOwner;

    function Ownable() public {
        owner = msg.sender;
    }

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    // Safe transfer of ownership in 2 steps. Once called, a newOwner needs to call claimOwnership() to prove ownership.
    function transferOwnership(address newOwner) public onlyOwner {
        pendingOwner = newOwner;
    }

    function claimOwnership() public {
        require(msg.sender == pendingOwner);
        owner = pendingOwner;
        pendingOwner = 0;
    }
}

contract MultiOwnable {

    mapping (address => bool) ownerMap;
    address[] public owners;

    event OwnerAdded(address indexed _newOwner);
    event OwnerRemoved(address indexed _oldOwner);

    modifier onlyOwner() {
        require(isOwner(msg.sender));
        _;
    }

    function MultiOwnable() public {
        // Add default owner
        address owner = msg.sender;
        ownerMap[owner] = true;
        owners.push(owner);
    }

    function ownerCount() public view returns (uint256) {
        return owners.length;
    }

    function isOwner(address owner) public view returns (bool) {
        return ownerMap[owner];
    }

    function addOwner(address owner) onlyOwner public returns (bool) {
        require(!isOwner(owner) && owner != 0);
        ownerMap[owner] = true;
        owners.push(owner);
        OwnerAdded(owner);
        return true;
    }

    function removeOwner(address owner) onlyOwner public returns (bool) {
        require(isOwner(owner));
        ownerMap[owner] = false;
        for (uint i = 0; i < owners.length - 1; i++) {
            if (owners[i] == owner) {
                owners[i] = owners[owners.length - 1];
                break;
            }
        }
        owners.length -= 1;
        OwnerRemoved(owner);
        return true;
    }
}

contract Pausable is Ownable {

    bool public paused;

    modifier ifNotPaused {
        require(!paused);
        _;
    }

    modifier ifPaused {
        require(paused);
        _;
    }

    // Called by the owner on emergency, triggers paused state
    function pause() external onlyOwner {
        paused = true;
    }

    // Called by the owner on end of emergency, returns to normal state
    function resume() external onlyOwner ifPaused {
        paused = false;
    }
}

contract BsToken is StandardToken, MultiOwnable {

    string public name;
    string public symbol;
    uint256 public totalSupply;
    uint8 public decimals = 18;
    string public version = 'v0.1';

    address public seller;     // The main account that holds all tokens at the beginning.

    uint256 public saleLimit;  // (e18) How many tokens can be sold in total through all tiers or tokensales.
    uint256 public tokensSold; // (e18) Number of tokens sold through all tiers or tokensales.

    bool public locked;

    event Sell(address indexed _seller, address indexed _buyer, uint256 _value);
    event SellerChanged(address indexed _oldSeller, address indexed _newSeller);

    event Lock();
    event Unlock();

    event Burn(address indexed _burner, uint256 _value);

    modifier onlyUnlocked() {
        require(isOwner(msg.sender) || !locked);
        _;
    }

    function BsToken(
        address _seller,
        string _name,
        string _symbol,
        uint256 _totalSupplyNoDecimals,
        uint256 _saleLimitNoDecimals
    ) public MultiOwnable() {

        // Lock the transfer function during the presale/crowdsale to prevent speculations.
        locked = true;

        seller = _seller;
        name = _name;
        symbol = _symbol;
        totalSupply = _totalSupplyNoDecimals * 1e18;
        saleLimit = _saleLimitNoDecimals * 1e18;

        balances[seller] = totalSupply;
        Transfer(0x0, seller, totalSupply);
    }

    function changeSeller(address newSeller) onlyOwner public returns (bool) {
        require(newSeller != 0x0 && seller != newSeller);

        address oldSeller = seller;
        uint256 unsoldTokens = balances[oldSeller];
        balances[oldSeller] = 0;
        balances[newSeller] = safeAdd(balances[newSeller], unsoldTokens);
        Transfer(oldSeller, newSeller, unsoldTokens);

        seller = newSeller;
        SellerChanged(oldSeller, newSeller);
        return true;
    }

    function sellNoDecimals(address _to, uint256 _value) public returns (bool) {
        return sell(_to, _value * 1e18);
    }

    function sell(address _to, uint256 _value) onlyOwner public returns (bool) {

        // Check that we are not out of limit and still can sell tokens:
        if (saleLimit > 0) require(safeSub(saleLimit, safeAdd(tokensSold, _value)) >= 0);

        require(_to != address(0));
        require(_value > 0);
        require(_value <= balances[seller]);

        balances[seller] = safeSub(balances[seller], _value);
        balances[_to] = safeAdd(balances[_to], _value);
        Transfer(seller, _to, _value);

        tokensSold = safeAdd(tokensSold, _value);
        Sell(seller, _to, _value);

        return true;
    }

    function transfer(address _to, uint256 _value) onlyUnlocked public returns (bool) {
        return super.transfer(_to, _value);
    }

    function transferFrom(address _from, address _to, uint256 _value) onlyUnlocked public returns (bool) {
        return super.transferFrom(_from, _to, _value);
    }

    function lock() onlyOwner public {
        locked = true;
        Lock();
    }

    function unlock() onlyOwner public {
        locked = false;
        Unlock();
    }

    function burn(uint256 _value) public returns (bool) {
        require(_value > 0);
        require(_value <= balances[msg.sender]);

        balances[msg.sender] = safeSub(balances[msg.sender], _value) ;
        totalSupply = safeSub(totalSupply, _value);
        Transfer(msg.sender, 0x0, _value);
        Burn(msg.sender, _value);

        return true;
    }
}

contract BsTokensale is SafeMath, Ownable, Pausable {

    BsToken public token;           // Token contract reference
    address public beneficiary;     // An ETH address that will receive all collected the ETH.

    uint256 public minAmountWei;    // Minimum amount to accept from contributors.
    uint256 public tokensPerEth;    // Default rate. Number of tokens per ETH.

    uint256 public totalTokensSold; // Total amount of tokens sold during this crowdsale.
    uint256 public maxCapInTokens;  // Maximum tokens to sell during this tokensale.

    uint256 public startTime;       // Crowdsale start time in seconds (will be compared with block time)
    uint256 public endTime;         // Crowdsale end time in seconds (will be compared with block time)

    event ChangeBeneficiaryEvent(address indexed _oldAddress, address indexed _newAddress);
    event ReceivedWeiEvent(address buyer, uint256 amountInWei);
    
    modifier respectTimeFrame() {
        require(startTime <= getNow() && getNow() <= endTime);
        _;
    }

    function BsTokensale(address _token, address _beneficiary) Ownable() public {
        token = BsToken(_token);
        beneficiary = _beneficiary;

        minAmountWei = 1 ether;
        tokensPerEth = 840; // Default rate
        maxCapInTokens = 17 * 1e6 ether; // 17 m tokens.

        startTime = 1517994000; // 2018-02-07T09:00:00Z
        endTime   = 1518166800; // 2018-02-09T09:00:00Z
    }

    function setBeneficiary(address _beneficiary) onlyOwner public {
        require(_beneficiary != address(0));
        require(_beneficiary != address(beneficiary));
        
        ChangeBeneficiaryEvent(beneficiary, _beneficiary);
        beneficiary = _beneficiary;
    }
    
    /*
     * The fallback function corresponds to a donation in ETH
     */
    function() public payable {
        sellTokensForETH(msg.sender, msg.value);
    }

    /*
     * Receives a donation in ETH
     */
    function sellTokensForETH(address buyer, uint256 amountInWei) internal ifNotPaused respectTimeFrame {
        _doSellTokens(buyer, amountInWei);
        _withdrawBalance();
        ReceivedWeiEvent(buyer, amountInWei);
    }

    function _doSellTokens(address buyer, uint256 amountInWei) internal returns (uint256 tokensSold) {
        require(amountInWei >= minAmountWei);

        tokensSold = weiToTokens(amountInWei);
        totalTokensSold = safeAdd(totalTokensSold, tokensSold);
        require(totalTokensSold <= maxCapInTokens);
        require(token.sell(buyer, tokensSold)); // Transfer tokens to buyer.
        
        return tokensSold;
    }
    
    // We override this method in tests to mock current time.
    function getNow() public view returns (uint256) {
        return now;
    }
    
    function weiToTokens(uint256 _weiValue) public view returns (uint256) {
        uint256 tokenRate = tokensPerEth;
        
        if (_weiValue >= 150 ether) {
            tokenRate = 1160;
        } else if (_weiValue >= 30 ether) {
            tokenRate = 1000;
        } else if(_weiValue >= 10 ether) {
            tokenRate = 920;
        }
        
        return safeMul(_weiValue, tokenRate);
    }

    function withdraw() public onlyOwner {
        _withdrawBalance();
    }
    
    function _withdrawBalance() internal {
        beneficiary.transfer(this.balance);
    }
}

contract BsTokenIssuer is SafeMath, Ownable {

    enum Currency { ETH, BTC, LTC, USD, EUR }

    /** Reasons why tx can be rejected. */
    uint8 public constant rejectionPresaleMinAmount = 1;   // Sent < 50k USD during presale.
    uint8 public constant rejectionCrowdsaleMinAmount = 2; // Sent < 15 USD during corwdsale.
    uint8 public constant rejectionOutOfTokens = 3;        // Not enough tokens left even if sent amount is above the min required amount.
    uint8 public constant rejectionOutOfTime = 4;          // Tx was sent between presale and crowdsale, or after corwdsale.
    uint8 public constant rejectionOther = 5;              // Other rejection (not expected).

    // currency_code => (tx_hash => tokens_e18)
    mapping(uint8 => mapping(bytes32 => uint256)) public acceptedTxs;
    
    // currency_code => (tx_hash => id_of_rejection_reason)
    mapping(uint8 => mapping(bytes32 => uint8)) public rejectedTxs;
    
    BsToken public token;
    
    // ETH address that is allowed to issue tokens or reject tx. 
    // A creator/owner of this contract can also issue tokens or reject tx.
    address public notifier;  

    // Stats
    uint256 public totalInWei = 0;
    uint256 public totalTokensSold = 0;
    uint256 public totalAcceptedTxs = 0; // Total amount of accepted external contributions (BTC, LTC, etc.)
    uint256 public totalRejectedTxs = 0;   // Total amount of rejected external txs.
    
    event NotifierChanged(address indexed _oldAddress, address indexed _newAddress);
    event TokensIssued(uint8 _currency, bytes32 _txIdSha3, address indexed _buyer, uint256 _amountWei, uint256 _tokensE18);
    event TxRejected(uint8 _currency, bytes32 _txIdSha3, uint8 _rejectionReason);

    modifier canNotify() {
        require(msg.sender == owner || msg.sender == notifier);
        _;
    }

    function BsTokenIssuer(address _token, address _notifier) Ownable() public {
        token = BsToken(_token);
        notifier = _notifier;
    }

    function setNotifier(address _notifier) public onlyOwner {
        NotifierChanged(notifier, _notifier);
        notifier = _notifier;
    }

    function issueTokens(
        uint8[]   _currencies,
        bytes32[] _txIdSha3,
        address[] _buyers,
        uint256[] _amountsWei,
        uint256[] _tokensE18,
        bool      _useRequire
    ) public canNotify {

        // All passed array-args should be not empty and have the same size:
        require(_currencies.length > 0);
        require(_currencies.length == _txIdSha3.length);
        require(_currencies.length == _buyers.length);
        require(_currencies.length == _amountsWei.length);
        require(_currencies.length == _tokensE18.length);

        for (uint i = 0; i < _txIdSha3.length; i++) {
            _issueTokensForOneTx(
                _currencies[i],
                _txIdSha3[i],
                _buyers[i],
                _amountsWei[i],
                _tokensE18[i],
                _useRequire
            );
        }
    }

    function _issueTokensForOneTx(
        uint8   _currency,
        bytes32 _txIdSha3, // To get bytes32 use keccak256(txId) OR sha3(txId)
        address _buyer,
        uint256 _amountWei,
        uint256 _tokensE18,
        bool    _useRequire
    ) internal {

        bool argsAreValid = _buyer > 0 && _amountWei > 0 && _tokensE18 > 0;
        if (_useRequire) require(argsAreValid);
        else if (!argsAreValid) return;

        // If this foreign transaction has been already processed in this contract.
        bool tokensAlreadyIssued = _isProcessedTx(_currency, _txIdSha3);
        if (_useRequire) require(!tokensAlreadyIssued);
        else if (tokensAlreadyIssued) return;
        
        var tokensIssued = token.sell(_buyer, _tokensE18);
        if (_useRequire) require(tokensIssued);
        else if (!tokensIssued) return;
        
        acceptedTxs[_currency][_txIdSha3] = _tokensE18;
        TokensIssued(_currency, _txIdSha3, _buyer, _amountWei, _tokensE18);
        
        // Update stats
        totalAcceptedTxs++;
        totalTokensSold = safeAdd(totalTokensSold, _tokensE18);
        totalInWei = safeAdd(totalInWei, _amountWei);
    }
    
    function rejectTx(
        uint8   _currency,
        bytes32 _txIdSha3, // To get bytes32 use keccak256(txId) OR sha3(txId)
        uint8   _rejectionReason,
        bool    _useRequire
    ) public canNotify {

        var argsAreValid = _rejectionReason > 0;
        if (_useRequire) require(argsAreValid);
        else if (!argsAreValid) return;
        
        // If this foreign transaction has been already rejected in this contract.
        bool txAlreadyRejected = _isProcessedTx(_currency, _txIdSha3);
        if (_useRequire) require(!txAlreadyRejected);
        else if (txAlreadyRejected) return;
        
        rejectedTxs[_currency][_txIdSha3] = _rejectionReason;
        TxRejected(_currency, _txIdSha3, _rejectionReason);
        
        // Update stats
        totalRejectedTxs++;
    }
    
    function _isProcessedTx(
        uint8   _currency,
        bytes32 _txIdSha3
    ) internal view returns (bool) {
        return 
            acceptedTxs[_currency][_txIdSha3] > 0 ||
            rejectedTxs[_currency][_txIdSha3] > 0;
    }
    
    function isProcessedTx(
        uint8  _currency,
        string _txId
    ) public view returns (bool) {
        return _isProcessedTx(_currency, keccak256(_txId));
    }
    
    /** 
     * Format of result array:
     * [
     *   N+0: tokens_issued_by_tx_N
     *   N+1: rejection_reason_by_tx_N
     *   ... repeat ...
     * ]
     */
    function checkTxs(
        uint8[]   _currencies,
        bytes32[] _txIdSha3
    ) public view returns (uint[] memory res) {

        require(_currencies.length > 0);
        require(_currencies.length == _txIdSha3.length);

        res = new uint[](_txIdSha3.length * 2);
        uint16 j = 0;
        for (uint i = 0; i < _txIdSha3.length; i++) {
            res[j++] = acceptedTxs[_currencies[i]][_txIdSha3[i]];
            res[j++] = rejectedTxs[_currencies[i]][_txIdSha3[i]];
        }
    }
    
    // Get id of currency enum. --------------------------------------------

    function ethId() public pure returns (uint8) {
        return uint8(Currency.ETH);
    }
    
    function btcId() public pure returns (uint8) {
        return uint8(Currency.BTC);
    }

    function ltcId() public pure returns (uint8) {
        return uint8(Currency.LTC);
    }

    function usdId() public pure returns (uint8) {
        return uint8(Currency.USD);
    }

    function eurId() public pure returns (uint8) {
        return uint8(Currency.EUR);
    }

    // Get token count by transaction id. ----------------------------------

    function _tokensByTx(Currency _currency, string _txId) internal view returns (uint256) {
        return tokensByTx(uint8(_currency), _txId);
    }

    function tokensByTx(uint8 _currency, string _txId) public view returns (uint256) {
        return acceptedTxs[_currency][keccak256(_txId)];
    }

    function tokensByEthTx(string _txId) public view returns (uint256) {
        return _tokensByTx(Currency.ETH, _txId);
    }
    
    function tokensByBtcTx(string _txId) public view returns (uint256) {
        return _tokensByTx(Currency.BTC, _txId);
    }

    function tokensByLtcTx(string _txId) public view returns (uint256) {
        return _tokensByTx(Currency.LTC, _txId);
    }

    function tokensByUsdTx(string _txId) public view returns (uint256) {
        return _tokensByTx(Currency.USD, _txId);
    }

    function tokensByEurTx(string _txId) public constant returns (uint256) {
        return _tokensByTx(Currency.EUR, _txId);
    }
}

contract TestTokenIssuer is BsTokenIssuer {

    function TestTokenIssuer(address _token) BsTokenIssuer(
        _token,
        msg.sender
    ) public {}
}

contract ProdTokenIssuer is BsTokenIssuer {

    function ProdTokenIssuer() BsTokenIssuer(
        0x123,      // TODO Set address of deployed token.
        msg.sender  // TODO Set address of notifier - address that will be able to issue tokens.
    ) public {}
}

contract ProdToken is BsToken {

    function ProdToken() BsToken(
        0x123, // TODO _seller address
        'Qurrex',
        'QRX',
        70000000,
        55000000
    ) public { }
}

contract ProdPrivateSale is BsTokensale {

    function ProdPrivateSale() BsTokensale(
        0x123, // TODO Token owner
        0x123  // TODO Beneficiary
    ) public { }
}
