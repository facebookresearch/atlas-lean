# Embedding a CCA adversary preserves its advantage

Let ciphertexts have decidable equality. For every private-key encryption scheme $S$ and every coin chosen-ciphertext adversary $A$, the [monadic CCA advantage](m-cca-advantage.md) of its [monadic form](of-coins-2.md) equals the CCA advantage of $A$. Both are $|\Pr[\text{game} = \text{true}] - \tfrac12|$ of the respective CCA game, in which stage-two decryption of the challenge returns $\bot$.
