# Strong duality between optimal mechanisms and optimal transport for a single additive buyer

For a single additive buyer with values in a box $X = \prod_j [x_j^{\mathrm{low}}, x_j^{\mathrm{high}}] \subseteq \mathbb{R}_{\ge 0}^n$, distributed (not necessarily independently) with a density $f$ that is continuous and differentiable with bounded derivatives, the optimal revenue equals the value of a dual problem: the minimum, over nonnegative measures $\gamma$ on $X \times X$ whose difference of marginals $\gamma_1 - \gamma_2$ convexly dominates the signed transformed measure $\mu_f$ derived from $f$ by integration by parts, of $\int \lVert x - y \rVert_1\, d\gamma(x, y)$. Both the primal supremum and the dual infimum are attained, and optimal mechanisms are characterized by complementary slackness with an optimal dual measure.

## Proof sketch

Express revenue of a mechanism through the buyer's convex utility function $u$ as $\int u\, d\mu_f$ by the envelope theorem and integration by parts. Optimizing over convex, nondecreasing, $1$-Lipschitz (with respect to the $\ell_1$ norm) $u$ is a linear program over a convex cone, whose dual is an optimal transport problem with a convex-dominance constraint. Weak duality is direct; strong duality follows from the Fenchel–Rockafellar duality theorem.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)

## Proof depends on

- [Payment formula](../../myerson-s-lemma-and-revenue-equivalence/payment-formula.md)

## Sources

- C. Daskalakis, A. Deckelbaum, C. Tzamos, "Strong Duality for a Multiple-Good Monopolist", Econometrica 85(3) (2017); EC 2015, arXiv:1409.4150, Theorems 1 and 2.
