# Carleson's theorem

Let $f \colon \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and square-integrable on $(0, 2\pi]$. Then the [symmetric Fourier partial sums](fourier-partial-sum.md) $S_N(f)(x) = \sum_{n=-N}^{N} \hat f_n e^{inx}$ converge to $f(x)$ for almost every $x \in \mathbb{R}$.

This is the theorem of L. Carleson, *On convergence and growth of partial sums of Fourier series*, Acta Math. 116 (1966), 135–157, which settled Luzin's conjecture; it is described in these terms in L. Becker et al., *Formalizing Carleson's theorem in Lean*, arXiv:2609.31334v1, §1.1. R. A. Hunt extended it to $L^p$ for $p > 1$ (same reference). C. Fefferman, *Pointwise convergence of Fourier series*, Ann. of Math. 98 (1973), 551–571, gave a second proof by decomposing the operator into time–frequency tiles.

Becker et al. treat, in their Theorem 2.2.1, the case of continuous $2\pi$-periodic $f$, with their own definition of the partial sums; the statement here assumes only $f \in L^2(0, 2\pi)$.

## Background

- [Fejér's theorem](fejer.md): for continuous $f$ the Cesàro means converge uniformly, whereas the partial sums themselves can diverge at points; Carleson's theorem says divergence happens only on a null set.

## Sources

- L. Becker et al., *Formalizing Carleson's theorem in Lean*, arXiv:2609.31334v1, §1.1 and Theorem 2.2.1.
- L. Carleson, *On convergence and growth of partial sums of Fourier series*, Acta Math. 116 (1966), 135–157 (original; not read for this page).
