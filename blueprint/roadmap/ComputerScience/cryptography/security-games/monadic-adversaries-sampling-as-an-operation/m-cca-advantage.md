# Monadic CCA advantage

For a private-key encryption scheme $S$ with decidable equality on ciphertexts and a [monadic CCA adversary](mccaadversary.md) $A$, the advantage is the real number

$$\left|\Pr[\text{the CCA game of } A \text{ returns true}] - \tfrac{1}{2}\right|,$$

where the game is the [monadic CCA game](m-cca-game.md). It is neither the raw winning probability nor twice this difference.
