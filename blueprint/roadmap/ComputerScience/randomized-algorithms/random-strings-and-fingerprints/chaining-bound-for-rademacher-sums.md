# Dudley's chaining bound for Rademacher sums

Let $(a_j)_{j \in J}$ be vectors in $\mathbb{R}^\kappa$ ($\kappa$ finite, $J$ arbitrary) with $\|a_j\|_2 \le r$, and let $T_0, T_1, \dots$ be finite sets of vectors such that every $a_j$ has a point of $T_n$ within Euclidean distance $r/2^n$. For a uniformly random sign vector $\sigma \in \{\pm1\}^\kappa$ and every $K \ge 0$,

$$
\mathbb{E}_\sigma \sup_{j} \sum_{i} a_{j,i}\sigma_i \le 2r\sqrt{2\log|T_0|} + \sum_{n<K}\frac{2r}{2^n}\sqrt{2\log(|T_{n+1}||T_n|)} + \frac{r}{2^K}\sqrt{|\kappa|} .
$$

When $|T_n|$ grows polynomially in $2^n$ the terms decay geometrically, removing the logarithmic factor of a single application of Massart's lemma (as for Rademacher complexity of VC classes).

## Proof sketch

Write $a_j$ as its level-$0$ approximation plus differences of consecutive approximations plus the level-$K$ error. The level-$0$ points have norm at most $2r$ and level-$n$ differences norm at most $2r/2^n$ and range over at most $|T_{n+1}||T_n|$ vectors, so Massart's lemma bounds each scale; Cauchy–Schwarz bounds the residual.

## Depends on

- [Massart's finite-class lemma](../../machine-learning/generalization-bounds-and-concentration/rademacher-complexity/rademacher-complexity-le-of-finite.md)
- [Exponential moment of a Rademacher sum](../../machine-learning/generalization-bounds-and-concentration/rademacher-complexity/average-exp-sign-corr-le.md)

## Proof depends on

- [Massart's finite-class lemma](../../machine-learning/generalization-bounds-and-concentration/rademacher-complexity/rademacher-complexity-le-of-finite.md)

## Sources

- R. M. Dudley, "The Sizes of Compact Subsets of Hilbert Space and Continuity of Gaussian Processes", Journal of Functional Analysis, 1967.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- R. Vershynin, "High-Dimensional Probability: An Introduction with Applications in Data Science", Cambridge University Press, 2018.
