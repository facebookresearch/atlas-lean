# Inclusion of L^q in L^p for finite measures

Let $\mu$ be a finite measure on a set $X$ with a σ-algebra, and let $0 \le p \le q \le \infty$. Then
$L^q(\mu) \subseteq L^p(\mu)$, for functions with values in $\mathbb{R}$, $\mathbb{C}$, a normed group or another space
with a continuous extended norm; for $p = 0$, membership in $L^0(\mu)$ asks only for almost everywhere strong
measurability. This is the general form of the inclusion $L^q(\mu) \subseteq L^p(\mu)$ for real or complex functions on
a finite measure space and $0 < p < q \le \infty$, which it gives by taking those values and exponents. The card's
second statement gives the bound behind the inclusion, for any measure and $p > 0$:
$\|f\|_p \le \|f\|_q \, \mu(X)^{1/p - 1/q}$ for every almost everywhere strongly measurable $f$, with $1/\infty = 0$.

## Idea

For $0 < p < q < \infty$, Hölder's inequality applied to $|f|^p \cdot 1$ with exponents $q/p$ and $q/(q-p)$ gives
$\int |f|^p \, d\mu \le \big(\int |f|^q \, d\mu\big)^{p/q} \mu(X)^{1 - p/q}$; for $q = \infty$ it is the bound
$|f|^p \le \|f\|_\infty^p$ almost everywhere. For an infinite measure the inclusion can fail: on $\mathbb{R}$ the
function $1/(1 + |x|)$ lies in $L^2$ but not in $L^1$, and for counting measure on $\mathbb{N}$ the inclusions go the
other way, $\ell^p \subseteq \ell^q$ for $0 < p \le q \le \infty$.

## Statements

- [$L^q \subseteq L^p$ for a finite measure and $p \le q$](mono-exponent.md)
- [Comparison of $L^p$ seminorms for $p \le q$](e-lp-norm-le-e-lp-norm-mul-rpow-measure-univ.md): the bound behind the inclusion, for any measure.

## Background

- [L^p spaces](../../normed-and-ordered-structure-of-lp-spaces/lp-space-of-a-measure/README.md): the $L^p$ seminorms
- [Hölder's inequality](../../h-lder-and-minkowski-inequalities-for-integrals/h-lder-s-inequality/README.md): used in the proof

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 7.10, for $0 < p < q < \infty$ (version read: the open-access PDF dated 12 June 2026).
