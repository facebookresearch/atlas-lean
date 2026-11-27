# Embedding a CCA adversary with explicit coins

Let ciphertexts have decidable equality. For every private-key encryption scheme $S$, every coin chosen-ciphertext adversary $A$ (coins in a type in the same universe as messages and ciphertexts) and each bit $b$, the [monadic CCA experiment](m-cca-exp.md) of its [monadic form](of-coins-2.md), whose coins are drawn by one sampling operation, equals the coin CCA experiment of $A$ with bit $b$, as distributions on guesses. In both, stage-two decryption of the challenge returns $\bot$.
