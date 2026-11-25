# Moran's equality for self-similar sets

Let $n \ge 1$ and let $f_0, \dots, f_{n-1}$ be maps of $\mathbb{R}^d$ of the form
$f_i(x) = \lambda A_i(x) + \beta_i$, with a common contraction factor $0 < \lambda < 1$, linear
isometries $A_i$ and vectors $\beta_i$. If the family satisfies the open set condition, then every
attractor $S$ of the family, that is every nonempty compact set with
$S = \bigcup_{i < n} f_i(S)$, has Hausdorff dimension

$$\dim_H S = -\frac{\log n}{\log \lambda}.$$

## Idea

An attractor is the union of $n$ copies of itself scaled by $\lambda$. If an $s$-dimensional
measure of $S$ were finite and positive and the copies did not overlap, scaling would give
$\mathcal{H}^s(S) = n \lambda^s \mathcal{H}^s(S)$, hence $n \lambda^s = 1$: this is the value of
$s$ in the formula. The open set condition is the hypothesis that keeps the overlaps negligible,
and the proof shows that $0 < \mathcal{H}^s(S) < \infty$ for this $s$. For the middle-thirds
Cantor set, $n = 2$ and $\lambda = 1/3$ give dimension $\log 2 / \log 3$.

## Statements

- [Moran's equality for affine-symmetric iterated function systems](moran-equality-affine.md)
- [Attractor of an iterated function system](is-attractor.md): the sets the theorem is about.
- [Open set condition](open-set-condition.md): the hypothesis of the theorem.
- [Affine-symmetric iterated function system](is-affine-symmetric-ifs.md): the systems the theorem covers.

## Sources

- P. A. P. Moran, *Additive functions of intervals and Hausdorff measure*, Proc. Cambridge Philos. Soc. 42 (1946).
- J. E. Hutchinson, *Fractals and self similarity*, Indiana Univ. Math. J. 30 (1981).
