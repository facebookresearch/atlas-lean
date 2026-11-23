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
applying the Poisson summation formula in $m$ to the others. The term of frequency $0$ produces the
pole, through $\zeta(2s - 1)$, and the constant term $c_0$ of the
[Laurent expansion of $\zeta$ at $1$](../../zeta-l-functions/riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullirec.md), which is
[Euler's constant](../../zeta-l-functions/riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullipol.md), brings in $\gamma$; the terms of nonzero frequency, computed at $s = 1$ by residues, add up to the
logarithm of the product defining $\eta$ (Siegel, pp. 11–13).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Laurent expansion of $\zeta$ at $s = 1$](../../zeta-l-functions/riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullirec.md), for its constant term $c_0$
- [Stieltjes constants exist, and the zeroth is Euler's constant](../../zeta-l-functions/riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullipol.md), for $c_0 = \gamma$
- [Even zeta values and Bernoulli numbers](../../zeta-l-functions/riemann-zeta/zeta-even-integers-bernoulli.md), for $\zeta(2) = \pi^2/6$
- [Residue theorem on a disc](../../../Analysis/complex-analysis/cauchy-theory/residue-theorem-closed-ball.md), for the integrals $\int_{\mathbb{R}} (1 + \xi^2)^{-1} e^{2\pi i k y \xi} \, d\xi$ at $s = 1$, computed from the residues at $\pm i$

## Sources

- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf> (copy:
  <https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf>), Chapter 1, §1:
  Theorem 1 (p. 13) and its proof, which uses Proposition 1 (the constant term of $\zeta$ at $s = 1$),
  formula (6) and Proposition 2 (Poisson summation); §2, formula (17) (p. 15).
