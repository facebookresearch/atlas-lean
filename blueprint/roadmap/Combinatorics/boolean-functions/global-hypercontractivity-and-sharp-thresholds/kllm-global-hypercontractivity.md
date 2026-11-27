# Keevash–Lifshitz–Long–Minzer: hypercontractivity for global functions

There is an absolute constant $C$ such that for every $0 < p \le 1/2$, every $r \ge 1$ and every $f : (\{0,1\}^n, \mu_p) \to \mathbb{R}$ of degree at most $r$ whose generalized influences satisfy $I_S(f) \le \delta$ for all $S$ with $|S| \le r$,

$$
\|f\|_4^4 \le C^{r}\, \delta\, \|f\|_2^2.
$$

Equivalently, for global functions the noise operator $T_\rho$ with an absolute constant $\rho$ (independent of $p$) is hypercontractive from $L^2$ to $L^4$ up to the globalness loss, in contrast with the general case.

## Proof sketch

Replace the $p$-biased cube by the uniform cube on $\{0,1\}^{n \times m}$ through a coupling in which each $p$-biased bit is a function of $m$ uniform bits; low-degree functions become low-degree functions whose influences are controlled by the generalized influences. Applying ordinary hypercontractivity on the uniform cube and expanding the fourth moment in terms of derivatives gives the bound, the globalness hypothesis controlling the terms that would otherwise blow up like $1/p$.

## Depends on

- [Global functions on the p-biased cube](pbiased-global-function.md)

## Proof depends on

- [Ordinary hypercontractivity degrades as p tends to zero](failure-of-hypercontractivity-small-p.md)

## Sources

- P. Keevash, N. Lifshitz, E. Long, D. Minzer, "Hypercontractivity for global functions and sharp thresholds", Journal of the American Mathematical Society 37 (2024), arXiv:1906.05568.
