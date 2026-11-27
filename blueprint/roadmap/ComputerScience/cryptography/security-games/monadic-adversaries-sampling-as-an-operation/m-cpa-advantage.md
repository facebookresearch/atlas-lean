# Monadic CPA advantage

For a private-key encryption scheme $S$ and a [monadic CPA adversary](mcpaadversary.md) $A$, the advantage is the real number

$$\left|\Pr[\text{the CPA game of } A \text{ returns true}] - \tfrac{1}{2}\right|,$$

where the game is the [monadic CPA game](m-cpa-game.md). It is neither the raw winning probability nor twice this difference.
