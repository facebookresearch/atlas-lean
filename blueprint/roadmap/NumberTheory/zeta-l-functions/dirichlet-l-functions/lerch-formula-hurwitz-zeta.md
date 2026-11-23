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
the integral converges locally uniformly in $(s, a)$ for $\operatorname{Re} s > -1$ together with its derivatives, so the
right-hand side is analytic in $s$ and $a$ jointly there, and it continues $\zeta(s, a)$. Setting $s = 0$ gives the first formula. For the second, the function
$f(a) = \frac{\partial \zeta}{\partial s}(0, a)$ satisfies $f(a + 1) = f(a) + \log a$, by differentiating
$\zeta(s, a) - \zeta(s, a + 1) = a^{-s}$ at $s = 0$, and it is convex on $(0, \infty)$: for $\operatorname{Re} s > 1$,
differentiating the series termwise gives $\frac{\partial^2 \zeta}{\partial a^2}(s, a) = s(s + 1) \zeta(s + 2, a)$, both sides
are analytic on $\{\operatorname{Re} s > -1, s \neq 1\}$, so the identity holds there, and differentiating it in $s$ at
$s = 0$, which commutes with $\partial^2 / \partial a^2$, gives $f''(a) = \zeta(2, a) > 0$. So $f(a) - f(1) = \log \Gamma(a)$ by the Bohr–Mollerup characterization of $\log \Gamma$, and
$f(1) = \zeta'(0) = -\frac{1}{2} \log (2\pi)$.

## Depends on

None.

## Proof depends on

- [Euler–Maclaurin formula](../../../Analysis/asymptotic-analysis/euler-maclaurin-formula.md), of order $2$ on $[0, N]$, for the representation of $\zeta(s, a)$

## Sources

- F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, Version 1.2.8 of
  2026-09-15, <https://dlmf.nist.gov/25.11>: equations 25.11.1 (definition), 25.11.6 (the representation above, for
  $s \neq 1$, $\operatorname{Re} s > -1$, $a > 0$), 25.11.13 ($\zeta(0, a) = \frac{1}{2} - a$) and 25.11.18
  ($\zeta'(0, a) = \ln \Gamma(a) - \frac{1}{2} \ln(2\pi)$, $a > 0$), and §25.11(i) (meromorphic continuation with a
  single simple pole at $s = 1$).
- E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 3rd edition, Cambridge University Press
  (1920), <https://archive.org/details/cu31924001549660>, §13.11 (the generalised zeta function, for
  $0 < a \le 1$) and §13.21 (p. 271): $\zeta(0, a) = \frac{1}{2} - a$ and
  $\bigl[\frac{d}{ds} \zeta(s, a)\bigr]_{s=0} = \log \Gamma(a) - \frac{1}{2} \log (2\pi)$, "previously obtained in a
  different manner by Lerch".
