# Monadic CPA indistinguishability game

For a private-key encryption scheme $S$ and a [monadic CPA adversary](mcpaadversary.md) $A$, the game draws a uniformly random bit $b$, runs the [fixed-bit experiment](m-cpa-exp.md) with $b$, and returns whether the adversary's guess equals $b$. It is a distribution on Booleans; its mass at true is the success probability. This is $\mathrm{PrivK}^{\mathrm{cpa}}$ of Katz and Lindell, Definition 3.22, for adversaries that sample on demand.
