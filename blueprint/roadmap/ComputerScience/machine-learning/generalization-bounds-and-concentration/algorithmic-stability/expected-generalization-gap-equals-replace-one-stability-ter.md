# Expected generalization gap equals replace-one stability term

For $m \ge 1$, a possibly randomized learner $A$, a distribution $D$ and a loss with all the expectations below finite,

$$\mathbb{E}_{S \sim D^m}\bigl[L_D(A(S)) - L_S(A(S))\bigr] = \mathbb{E}\bigl[\ell(A(S^{(i)}), z_i) - \ell(A(S), z_i)\bigr],$$

where on the right $S \sim D^m$, $z' \sim D$ and $i$ uniform on $\{1, \dots, m\}$ are independent, $S^{(i)}$ replaces $z_i$
by $z'$, and both sides also average over $A$'s randomness (Shalev-Shwartz and Ben-David, Theorem 13.2).

## Depends on

- [On-average replace-one stability](on-average-replace-one-stability.md)
- [Expected risk](../risk.md)
- [Empirical risk](../empirical-risk.md)

## Proof depends on

- [Replace-one sampling preserves the law of an i.i.d. sample](map-update-prod-pi.md)

## Sources

- Understanding Machine Learning: From Theory to Algorithms — Shalev-Shwartz, Ben-David / Cambridge University Press, Theorem 13.2. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
