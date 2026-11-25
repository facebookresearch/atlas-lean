# Junction gap is unchanged by doubling for distinct nonzero magnitudes

For integers $p$ and $q$ with $|p| \ge 1$, $|q| \ge 1$ and $|p| \ne |q|$, let
$\delta(p) = (\delta_1(p), \delta_2(p))$ and $\delta(q) = (\delta_1(q), \delta_2(q))$ be their
[doubled pairs](dbl-one.md). The [gap indicator](is-gap.md) of the junction
$(\delta_2(p), \delta_1(q))$ equals the [directed gap indicator](is-dir-gap.md) of $(p, q)$:
$|\delta_1(q) - \delta_2(p)| = 1$ if and only if $q - p = 1$. So in the doubled list of a
[signed permutation](svalid.md), the junction between two consecutive doubled pairs is a breakpoint
exactly when the two signed entries form a signed breakpoint (Shamir and Peer, Lecture 11, signed
setting). Without the hypotheses the equality can fail: for $p = q = 1$ the junction $(2, 1)$ is not
a gap but $q - p = 0$, and for $p = -1$, $q = 0$ the junction $(1, -1)$ is a gap but $q - p = 1$.
