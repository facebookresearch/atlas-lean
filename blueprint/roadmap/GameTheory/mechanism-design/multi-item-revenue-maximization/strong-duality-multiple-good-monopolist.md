# Strong duality between optimal mechanisms and optimal transport for a single additive buyer

For a single additive buyer with values in $[0, M]^n$ distributed with a sufficiently regular density $f$, the optimal revenue equals the value of a dual problem: the minimum, over measures $\gamma$ on $[0, M]^n \times [0, M]^n$ whose difference of marginals dominates (in convex order) the signed transformed measure $\mu_f$ derived from $f$ by integration by parts, of $\int \lVert x - y \rVert_1^{+}\, d\gamma(x, y)$ with $\lVert z \rVert_1^{+} = \sum_j \max(z_j, 0)$. Optimal mechanisms are characterized by complementary slackness with an optimal transport plan.

## Proof sketch

Express revenue of a mechanism through the buyer's convex utility function $u$ as $\int u\, d\mu_f$ by the envelope theorem and integration by parts. Optimizing over convex $1$-Lipschitz (in the appropriate norm) $u$ is a linear program over a convex cone, whose dual is an optimal transport problem with a convex-order constraint; strong duality follows from a minimax theorem for this conic problem.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)

## Proof depends on

- [Payment formula](../myerson-s-lemma-and-revenue-equivalence/payment-formula.md)

## Sources

- C. Daskalakis, A. Deckelbaum, C. Tzamos, "Strong Duality for a Multiple-Good Monopolist", Econometrica 85(3) (2017); EC 2015.
