# Embedding a public-key CCA adversary with explicit coins

Let ciphertexts have decidable equality. For every public-key encryption scheme $S$, every coin public-key chosen-ciphertext adversary $A$ and each bit $b$, the [monadic public-key CCA experiment](m-pub-cca-exp.md) of its [monadic form](of-coins-3.md), which draws its coins by one sampling operation after receiving the public key, equals the coin public-key CCA experiment of $A$ with bit $b$, as distributions on guesses. In both, stage-two decryption of the challenge returns $\bot$.
