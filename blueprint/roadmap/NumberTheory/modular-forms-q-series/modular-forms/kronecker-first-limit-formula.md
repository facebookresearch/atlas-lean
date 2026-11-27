# Kronecker's first limit formula

For $z = x + iy$ with $y > 0$, let $Q_z(u, v) = y^{-1} |u + v z|^2$, a positive definite binary
quadratic form of determinant $1$, and let

$$Z(z, s) = \sum_{(m, n) \neq (0, 0)} Q_z(m, n)^{-s} = \sum_{(m, n) \neq (0, 0)} \frac{y^s}{|m + n z|^{2s}} \qquad (\operatorname{Re} s > 1)$$

be its Epstein zeta function, the sum running over the pairs of integers other than $(0, 0)$; the
series converges absolutely, and uniformly in every half-plane $\operatorname{Re} s \ge 1 + \varepsilon$
with $\varepsilon > 0$. Then $Z(z, s)$ continues analytically to the half-plane $\operatorname{Re} s > 1/2$,
except for a simple pole at $s = 1$ with residue $\pi$, and

$$\lim_{s \to 1} \left( Z(z, s) - \frac{\pi}{s - 1} \right) = 2\pi \left( \gamma - \log 2 - \log\bigl(\sqrt{y}\, |\eta(z)|^2\bigr) \right),$$

where $\gamma$ is Euler's constant and $\eta(z) = e^{\pi i z / 12} \prod_{n \ge 1} (1 - e^{2\pi i n z})$
is the Dedekind eta function.

The sum $Z(z, s)$ does not change when $z$ is replaced by $(az + b)/(cz + d)$ with
$\left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right) \in \mathrm{SL}_2(\mathbb{Z})$, since
$(m, n) \mapsto (md + nb, mc + na)$ permutes the nonzero pairs of integers, so the formula shows that
$y^{1/4} |\eta(z)|$, and hence $\operatorname{Im}(z) |\eta(z)|^4$, is invariant under $\mathrm{SL}_2(\mathbb{Z})$
(Siegel, Chapter 1, §2, formula (17)).

Siegel proves the formula by separating the terms with $n = 0$, which give $2 y^s \zeta(2s)$, equal to $\pi^2 y / 3$
at $s = 1$ by the [even zeta value](../../zeta-l-functions/riemann-zeta/zeta-even-integers-bernoulli.md) $\zeta(2) = \pi^2/6$, and
applying the [Poisson summation formula](../../../Analysis/harmonic-analysis/fourier-series/poisson-summation-formula.md) in $m$
to the others. The terms with $n$ and $-n$ are equal, and for $n \ge 1$ the function $\xi \mapsto |\xi + i n y|^{-2s}$ is
continuous and $O(|\xi|^{-2 \operatorname{Re} s})$, while its Fourier transform decays exponentially (by the shift of the line
of integration below, which applies to every real frequency), so

$$\sum_{m \in \mathbb{Z}} |m + n z|^{-2s} = (n y)^{1 - 2s} \sum_{k \in \mathbb{Z}} e^{-2\pi i k n x} \int_{\mathbb{R}} (1 + \xi^2)^{-s} e^{2\pi i k n y \xi} \, d\xi.$$

The term of frequency $k = 0$ is $(n y)^{1 - 2s} \, \mathrm{B}(\tfrac{1}{2}, s - \tfrac{1}{2}) = (n y)^{1 - 2s} \sqrt{\pi} \, \Gamma(s - \tfrac{1}{2}) / \Gamma(s)$,
by the substitutions $\xi^2 = \lambda$ and $\lambda = \mu / (1 - \mu)$, the
[beta integral](../../../Analysis/special-functions/gamma-function/gamma-beta-relation.md) and
[$\Gamma(\tfrac{1}{2}) = \sqrt{\pi}$](../../../Analysis/sequences-and-series/trigonometric-and-harmonic-series/series-from-n-rlund-s-digamma-identity/gamma-add-half-and-gamma-half-sub-nat.md);
summed over $n \ge 1$ with the factor $2 y^s$, these terms give $2 y^{1 - s} \sqrt{\pi} \, \Gamma(s - \tfrac{1}{2}) \Gamma(s)^{-1} \zeta(2s - 1)$. For $k \neq 0$ and
$\operatorname{Re} s > \frac{1}{2}$, the integrand $(1 + \zeta^2)^{-s} e^{2\pi i k n y \zeta}$ is holomorphic on the strip
$0 \le \operatorname{sign}(k) \operatorname{Im} \zeta \le \frac{1}{2}$, where $\operatorname{Re}(1 + \zeta^2) \ge \frac{3}{4}$, so the
[Cauchy–Goursat theorem for rectangles](../../../Analysis/complex-analysis/cauchy-theory/contour-integrals-over-rectangles/boundary-integral-eq-zero.md),
applied to $[-R, R] \times [0, \pm \frac{1}{2}]$, whose vertical sides contribute $O(R^{-2 \operatorname{Re} s})$, moves the line of
integration to $\operatorname{Im} \zeta = \operatorname{sign}(k)/2$. On that line $|e^{2\pi i k n y \zeta}| = e^{-\pi |k| n y}$ and
$|(1 + \zeta^2)^{-s}| \le e^{\pi |\operatorname{Im} s| / 2} \bigl((\operatorname{Re} \zeta)^2 + \frac{3}{4}\bigr)^{-\operatorname{Re} s}$, an integrable
function of $\operatorname{Re} \zeta$; so the integral, the sum of the integrals over the segments of length $1$ of that line, is a
[holomorphic](../../../Analysis/complex-analysis/cauchy-theory/holomorphic-sum-of-dominated-series.md) function of $s$ on
$\operatorname{Re} s > \frac{1}{2}$, bounded by $C e^{-\pi |k| n y}$ for $s$ in a compact subset. (Siegel obtains these bounds,
his (11) and (12), for all $s$ by moving the line instead to the two banks of the cut from $\pm i$ to $\pm i\infty$, joined by a
circle of radius $\frac{1}{2}$ around $\pm i$, which makes these terms entire.) So the terms of nonzero frequency form a double
series of holomorphic functions on $\operatorname{Re} s > \frac{1}{2}$, dominated on each compact subset by a convergent series
$C \sum_{n \ge 1} \sum_{k \neq 0} e^{-\pi |k| n y}$, as $|y^s (n y)^{1 - 2s}| \le y^{1 - \operatorname{Re} s}$, and their sum is
holomorphic there by the same theorem. Hence $Z(z, s)$ continues to the
half-plane $\operatorname{Re} s > 1/2$, where $\zeta(2s)$ is holomorphic and so is $\Gamma(s - \tfrac{1}{2}) / \Gamma(s)$, as
$\Gamma$ is [analytic away from the nonpositive integers](../../../Analysis/special-functions/gamma-function/digamma-and-trigamma-functions/analytic-at-gamma.md)
and [has no zeros](../../../Analysis/special-functions/gamma-function/gamma-function-no-zeros.md); its value at $s = 1$ is $\sqrt{\pi}$, as
$\Gamma(1) = \int_0^\infty e^{-t} \, dt = 1$. The only pole is that of $\zeta(2s - 1)$ at $s = 1$, whose residue is $\frac{1}{2}$ by the
[Laurent expansion of $\zeta$ at $1$](../../zeta-l-functions/riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullirec.md),
so $Z(z, s)$ has residue $2 \sqrt{\pi} \cdot \sqrt{\pi} \cdot \frac{1}{2} = \pi$ there.

For the constant term, the [duplication formula](../../../Analysis/sequences-and-series/trigonometric-and-harmonic-series/series-from-n-rlund-s-digamma-identity/gamma-add-half-and-gamma-half-sub-nat.md)
at $r = s - 1$ gives $\Gamma(s - \tfrac{1}{2}) / \Gamma(s) = \sqrt{\pi} \, 2^{2 - 2s} \, \Gamma(2s - 1) / \Gamma(s)^2$, and
$\Gamma(2s - 1) / \Gamma(s)^2 = 1 + O((s - 1)^2)$ by the analyticity of $\Gamma$ at $1$. With the constant term $c_0$ of the
Laurent expansion, which is [Euler's constant](../../zeta-l-functions/riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullipol.md),
the term of frequency $0$ is $\pi / (s - 1) + 2\pi(\gamma - \log(2\sqrt{y})) + O(s - 1)$. The terms of nonzero frequency at
$s = 1$ follow from the residues at $\pm i$, $\int_{\mathbb{R}} (1 + \xi^2)^{-1} e^{2\pi i a \xi} \, d\xi = \pi e^{-2\pi |a|}$
for real $a$, and summing them with $\sum_{n \ge 1} q^n / n = -\log(1 - q)$ gives the logarithm of the product defining
$\eta$ (Siegel, pp. 6–13).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Poisson summation formula for functions with power decay](../../../Analysis/harmonic-analysis/fourier-series/poisson-summation-formula.md), in $m$, for the terms with $n \neq 0$
- [The beta integral in terms of the gamma function](../../../Analysis/special-functions/gamma-function/gamma-beta-relation.md), for the term of frequency $0$
- [The Gamma function at $r + \tfrac12$ and at $\tfrac12 - r$](../../../Analysis/sequences-and-series/trigonometric-and-harmonic-series/series-from-n-rlund-s-digamma-identity/gamma-add-half-and-gamma-half-sub-nat.md), for $\Gamma(\tfrac{1}{2}) = \sqrt{\pi}$ and, at $r = s - 1$, for the duplication formula
- [Cauchy–Goursat theorem for rectangles](../../../Analysis/complex-analysis/cauchy-theory/contour-integrals-over-rectangles/boundary-integral-eq-zero.md), for moving the line of integration to $\operatorname{Im} \zeta = \pm \frac{1}{2}$
- [A dominated series of holomorphic functions is holomorphic](../../../Analysis/complex-analysis/cauchy-theory/holomorphic-sum-of-dominated-series.md), for the integrals of nonzero frequency and their sum
- [Analyticity of the Gamma function](../../../Analysis/special-functions/gamma-function/digamma-and-trigamma-functions/analytic-at-gamma.md), for the regularity of $\Gamma(s - \tfrac{1}{2})$ and the expansion of $\Gamma$ at $1$
- [The complex gamma function has no zeros away from its poles](../../../Analysis/special-functions/gamma-function/gamma-function-no-zeros.md), for the regularity of $1 / \Gamma(s)$
- [Laurent expansion of $\zeta$ at $s = 1$](../../zeta-l-functions/riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullirec.md), for the pole of $\zeta(2s - 1)$ and its constant term $c_0$
- [Stieltjes constants exist, and the zeroth is Euler's constant](../../zeta-l-functions/riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullipol.md), for $c_0 = \gamma$
- [Even zeta values and Bernoulli numbers](../../zeta-l-functions/riemann-zeta/zeta-even-integers-bernoulli.md), for $\zeta(2) = \pi^2/6$
- [Residue theorem on a disc](../../../Analysis/complex-analysis/cauchy-theory/residue-theorem-closed-ball.md), for the integrals $\int_{\mathbb{R}} (1 + \xi^2)^{-1} e^{2\pi i a \xi} \, d\xi$, computed from the residues at $\pm i$

## Sources

- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf> (copy:
  <https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf>), Chapter 1, §1:
  Theorem 1 (p. 13) and its proof, which uses Proposition 1 (the constant term of $\zeta$ at $s = 1$),
  formula (6), Proposition 2 (Poisson summation), formulas (8)–(13) (pp. 6–10: the beta integral, the contours $\Gamma_\pm$
  of Fig. 1 along the banks of the cuts from $\pm i$ with a circle of radius $\frac{1}{2}$ around $\pm i$, the estimates (11)
  and (12), and the theorem of Weierstrass) and the duplication formula (p. 11); §2, formula (17) (p. 15).
