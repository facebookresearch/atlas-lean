# Lerch's formula for the Hurwitz zeta function at $s = 0$

For $a > 0$ let $\zeta(s, a) = \sum_{n \ge 0} (n + a)^{-s}$ $(\operatorname{Re} s > 1)$ be the Hurwitz zeta function,
continued meromorphically to $\mathbb{C}$, where its only pole is a simple pole at $s = 1$. Then

$$\zeta(0, a) = \frac{1}{2} - a, \qquad \frac{\partial \zeta}{\partial s}(0, a) = \log \Gamma(a) - \frac{1}{2} \log (2\pi).$$

For $a = 1$ these are $\zeta(0) = -\frac{1}{2}$ and $\zeta'(0) = -\frac{1}{2} \log (2\pi)$.

For $a > 0$ and $s \neq 1$ with $\operatorname{Re} s > -1$,

$$\zeta(s, a) = a^{-s} \left( \frac{1}{2} + \frac{a}{s - 1} \right) - \frac{s (s + 1)}{2} \int_0^\infty \frac{\widetilde{B}_2(x) - B_2}{(x + a)^{s + 2}} \, dx,$$

where $\widetilde{B}_2(x) = B_2(x - \lfloor x \rfloor)$ is the periodic Bernoulli function and $B_2 = 1/6$. For
$\operatorname{Re} s > 1$ this follows from the [Euler–Maclaurin formula](../../../Analysis/asymptotic-analysis/euler-maclaurin-formula.md)
of order $2$, applied on $[0, N]$ to the real and imaginary parts of $x \mapsto (x + a)^{-s}$, by letting $N \to \infty$;
the integral converges absolutely and locally uniformly in $(s, a)$ for $\operatorname{Re} s > -1$, together with its derivatives,
so the right-hand side is smooth in $(s, a)$ and, as the sum of the integrals over the intervals $[n, n + 1]$,
[holomorphic](../../../Analysis/complex-analysis/cauchy-theory/holomorphic-sum-of-dominated-series.md) in $s$; by the
[identity theorem](../../../Geometry/complex-and-symplectic-geometry/identity-and-open-mapping-theorems-for-holomorph/holomorphic-identity-on-connected-comple.md) it is the continuation of $\zeta(s, a)$. Setting $s = 0$ gives the first formula. For the second, the function
$f(a) = \frac{\partial \zeta}{\partial s}(0, a)$ satisfies $f(a + 1) = f(a) + \log a$, by differentiating
$\zeta(s, a) - \zeta(s, a + 1) = a^{-s}$ at $s = 0$, and it is convex on $(0, \infty)$: for $\operatorname{Re} s > 1$,
differentiating the series termwise gives $\frac{\partial^2 \zeta}{\partial a^2}(s, a) = s(s + 1) \zeta(s + 2, a)$, both sides
are holomorphic in $s$ on $\{\operatorname{Re} s > -1, s \neq 1\}$, so the identity holds there by the identity theorem, and
differentiating it in $s$ at $s = 0$, which commutes with $\partial^2 / \partial a^2$ by
[Clairaut's theorem](../../../Analysis/real-functions/multivariable-calculus/partial-derivatives-and-symmetry-of-mixed-partia/iterated-partial-deriv-commute.md)
applied twice, to $\partial \zeta / \partial a$ and then to $\zeta$, for the restriction $(x, a) \mapsto \zeta(x, a)$ to real
$x$ near $0$ and $a > 0$ (a smooth real function, after a smooth cutoff, whose $x$-derivative is the complex derivative in $s$),
gives $f''(a) = \zeta(2, a) > 0$. So $F(a) = e^{f(a) - f(1)}$ is a
positive function on $(0, \infty)$ with $F(1) = 1$, $F(a + 1) = a F(a)$ and $\log F$ convex, and the
[Bohr–Mollerup theorem](../../../Analysis/special-functions/gamma-function/bohr-mollerup-theorem.md)
gives $F = \Gamma$, that is, $f(a) = \log \Gamma(a) + f(1)$. To find $f(1)$, note that
$\zeta(s, \tfrac{1}{2}) = \sum_{n \ge 0} 2^s (2n + 1)^{-s} = (2^s - 1) \zeta(s)$ for $\operatorname{Re} s > 1$, hence for all
$s \neq 1$ by the identity theorem;
differentiating at $s = 0$, with $\zeta(0) = \zeta(0, 1) = -\frac{1}{2}$ by the first formula, gives
$f(\tfrac{1}{2}) = -\frac{1}{2} \log 2$. As [$\Gamma(\tfrac{1}{2}) = \sqrt{\pi}$](../../../Analysis/sequences-and-series/trigonometric-and-harmonic-series/series-from-n-rlund-s-digamma-identity/gamma-add-half-and-gamma-half-sub-nat.md),
$f(1) = f(\tfrac{1}{2}) - \log \Gamma(\tfrac{1}{2}) = -\frac{1}{2} \log (2\pi)$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Euler–Maclaurin formula](../../../Analysis/asymptotic-analysis/euler-maclaurin-formula.md), of order $2$ on $[0, N]$, for the representation of $\zeta(s, a)$
- [The Gamma function at $r + \tfrac12$ and at $\tfrac12 - r$](../../../Analysis/sequences-and-series/trigonometric-and-harmonic-series/series-from-n-rlund-s-digamma-identity/gamma-add-half-and-gamma-half-sub-nat.md), at $r = 0$, for $\Gamma(\tfrac{1}{2}) = \sqrt{\pi}$
- [A dominated series of holomorphic functions is holomorphic](../../../Analysis/complex-analysis/cauchy-theory/holomorphic-sum-of-dominated-series.md), for the holomorphy in $s$ of the integral
- [Identity theorem for holomorphic maps](../../../Geometry/complex-and-symplectic-geometry/identity-and-open-mapping-theorems-for-holomorph/holomorphic-identity-on-connected-comple.md), for the continuation of $\zeta(s, a)$ and the identities extended from $\operatorname{Re} s > 1$
- [Symmetry of mixed partial derivatives (Clairaut's theorem)](../../../Analysis/real-functions/multivariable-calculus/partial-derivatives-and-symmetry-of-mixed-partia/iterated-partial-deriv-commute.md), for exchanging $\partial / \partial s$ and $\partial^2 / \partial a^2$
- [Bohr–Mollerup theorem](../../../Analysis/special-functions/gamma-function/bohr-mollerup-theorem.md), for $F = \Gamma$

## Sources

- F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, Version 1.2.8 of
  2026-09-15, <https://dlmf.nist.gov/25.11>: equations 25.11.1 (definition), 25.11.6 (the representation above, for
  $s \neq 1$, $\operatorname{Re} s > -1$, $a > 0$), 25.11.13 ($\zeta(0, a) = \frac{1}{2} - a$) and 25.11.18
  ($\zeta'(0, a) = \ln \Gamma(a) - \frac{1}{2} \ln(2\pi)$, $a > 0$), and §25.11(i) (meromorphic continuation with a
  single simple pole at $s = 1$); <https://dlmf.nist.gov/5.5>, §5.5(iv) (the Bohr–Mollerup theorem: a positive
  function $f$ on $(0, \infty)$ with $f(x + 1) = x f(x)$, $f(1) = 1$ and $\ln f$ convex is $\Gamma$).
- E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 3rd edition, Cambridge University Press
  (1920), <https://archive.org/details/cu31924001549660>, §13.11 (the generalised zeta function, for
  $0 < a \le 1$) and §13.21 (p. 271): $\zeta(0, a) = \frac{1}{2} - a$ and
  $\bigl[\frac{d}{ds} \zeta(s, a)\bigr]_{s=0} = \log \Gamma(a) - \frac{1}{2} \log (2\pi)$, "previously obtained in a
  different manner by Lerch".
