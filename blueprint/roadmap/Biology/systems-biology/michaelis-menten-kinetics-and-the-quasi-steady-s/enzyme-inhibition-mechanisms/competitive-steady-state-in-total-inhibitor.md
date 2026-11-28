# Competitive steady state in terms of total inhibitor

With total rather than free inhibitor given, the competitive steady state is fixed by a quadratic for bound inhibitor. At positive substrate, inserting total inhibitor into the free-inhibitor rate law underestimates the rate whenever inhibitor is present. The bound fraction of total inhibitor is at most total enzyme over total inhibitor.

Let $k_1, k_2, k_3, k_{-3} > 0$ and $k_{-1} \ge 0$ be the constants of the
[competitive mechanism](competitive-inhibition-mechanism.md), $K_M = (k_{-1} + k_2)/k_1$,
$K_I = k_{-3}/k_3$, and let $e_T > 0$ (total enzyme), $i_T \ge 0$ (total inhibitor) and a fixed free
substrate level $s \ge 0$ be given.

*Steady-state premise with conserved inhibitor.* Nonnegative $(e, c, y, i)$ satisfy

$$k_1 e s - (k_{-1} + k_2)c = 0, \qquad k_3 e i - k_{-3} y = 0, \qquad e + c + y = e_T, \qquad i + y = i_T .$$

Put $K_{\mathrm{app}} = K_I(1 + s/K_M)$ and $b = e_T + i_T + K_{\mathrm{app}}$. Then there is exactly
one such quadruple, given by

$$y = \frac{b - \sqrt{b^2 - 4\, e_T\, i_T}}{2}, \qquad i = i_T - y, \qquad e = \frac{e_T - y}{1 + s/K_M}, \qquad c = \frac{s}{K_M}\, e,$$

with $0 \le y \le \min(e_T, i_T)$; the other root of
$y^2 - b\, y + e_T i_T = 0$ exceeds $\max(e_T, i_T)$ when $i_T > 0$. The product rate $v = k_2 c$
satisfies

$$v = v_0 \left(1 - \frac{y}{e_T}\right), \qquad v_0 = \frac{k_2\, e_T\, s}{K_M + s},$$

and $v$ equals the
[competitive steady-state law](steady-state-rate-law-of-competitive-inhibition.md) evaluated at the
**free** inhibitor $i$. If $s > 0$, the same law evaluated at the total $i_T$ is at most $v$, with
equality exactly when $i_T = 0$. Moreover $0 \le i_T - i = y \le e_T$, so for $i_T > 0$ the bound fraction of total inhibitor satisfies $(i_T-i)/i_T\le e_T/i_T$. This normalizes by the total, not by the free concentration.

## Depends on

- [Competitive-inhibition mechanism](competitive-inhibition-mechanism.md)
- [Conserved totals of the inhibition mechanisms](conserved-totals-of-inhibition-mechanisms.md)
- [Steady-state rate law of competitive inhibition](steady-state-rate-law-of-competitive-inhibition.md)

## Proof depends on

- [Steady-state rate law of competitive inhibition](steady-state-rate-law-of-competitive-inhibition.md)
- [Conserved totals of the inhibition mechanisms](conserved-totals-of-inhibition-mechanisms.md)

## Expansion

The first and third equations give $e = (e_T - y)/(1 + s/K_M)$; the second, with $i = i_T - y$, gives
$y K_{\mathrm{app}} = (e_T - y)(i_T - y)$, the quadratic. With $f(y) = y^2 - b y + e_T i_T$ and
$m = \min(e_T, i_T)$, $M = \max(e_T, i_T)$: $f(0) = e_T i_T \ge 0$, $f(m) = -K_{\mathrm{app}} m \le 0$
and $f(M) = -K_{\mathrm{app}} M < 0$ for $M > 0$, so the smaller root lies in $[0, m]$ and the larger
exceeds $M$ when $i_T > 0$; nonnegativity of $i$ and $e$ forces the smaller root. Then
$v = k_2 s (e_T - y)/(K_M + s)$. Given $(e, c, y)$ at free inhibitor $i$, the competitive law gives
the same $v$, and that law is strictly decreasing in $i$ when $s > 0$; since $i \le i_T$, with equality
iff $y = 0$, and $y > 0$ whenever $i_T > 0$ (because $f(0) > 0$), the inequality follows.

A numerical illustration: for $e_T = i_T$, $K_I = 0.01\, e_T$ and $s = K_M$, the free inhibitor is
about $0.13\, i_T$ and $v/v_0 \approx 0.13$, while the law at total inhibitor predicts
$v/v_0 \approx 0.02$. The free-inhibitor form is the competitive law; the total-inhibitor
substitution is an approximation valid when inhibitor greatly exceeds enzyme. In the singular
perturbation limit of small enzyme the reduced rate contains the total inhibitor, consistent with
$y \le e_T \to 0$.

## Sources

- A. Pesaresi, "Mixed and non-competitive enzyme inhibition: underlying mechanisms and mechanistic
  irrelevance of the formal two-site model", *Journal of Enzyme Inhibition and Medicinal Chemistry*
  38(1) (2023) 2245168, Results, "Case I – tight-binding inhibitors" and Figure 3(A) (inhibitor
  depletion when $[I]/[E]$ falls below about $10$ makes a competitive inhibitor look mixed),
  <https://doi.org/10.1080/14756366.2023.2245168>.
- J. Eilertsen, S. Schnell and S. Walcher, *Bulletin of Mathematical Biology* 85 (2023), article 48, <https://doi.org/10.1007/s11538-023-01150-7>; locators from the version read, arXiv:2211.10836v2 (2023), Section 6.3, Eqs. (75) and (77)
  (free inhibitor $i_0 - c_2$ in the full system, total $i_0$ in the small-enzyme reduction),
  <https://arxiv.org/abs/2211.10836v2>.
- NC-IUB Panel on Enzyme Kinetics (A. Cornish-Bowden, H. B. F. Dixon, K. J. Laidler, I. H. Segel,
  J. Ricard, S. F. Velick and E. C. Webb), "Symbolism and terminology in enzyme kinetics,
  Recommendations 1981", *European Journal of Biochemistry* 128 (1982) 281–291; web version
  Section 6.1 (tight-binding inhibitors), <https://iubmb.qmul.ac.uk/kinetics/ek4t6.html>.
