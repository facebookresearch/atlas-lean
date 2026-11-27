# Monadic CCA indistinguishability game

For a private-key encryption scheme $S$ with decidable equality on ciphertexts and a [monadic CCA adversary](mccaadversary.md) $A$, the game draws a uniformly random bit $b$, runs the [fixed-bit experiment](m-cca-exp.md) with $b$ (in which stage-two decryption of the challenge returns $\bot$), and returns whether the guess equals $b$. It is a distribution on Booleans; its mass at true is the success probability. This is $\mathrm{PrivK}^{\mathrm{cca}}$ of Katz and Lindell, Definition 3.33, for adversaries that sample on demand.
