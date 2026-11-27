# Embedding a CPA adversary with explicit coins

For every private-key encryption scheme $S$, every coin CPA adversary $A$ (coins in a type in the same universe as messages and ciphertexts) and each bit $b$, the [monadic CPA experiment](m-cpa-exp.md) of its [monadic form](of-coins.md) with bit $b$ equals the coin CPA experiment of $A$ with bit $b$, as distributions on guesses. The coin experiment samples the key, then the coins once, and runs both stages on those coins.
