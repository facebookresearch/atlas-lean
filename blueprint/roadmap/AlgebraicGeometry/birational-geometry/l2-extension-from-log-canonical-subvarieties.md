# L² extension from subvarieties defined by log canonical weights

Let $X$ be a weakly pseudoconvex Kähler manifold of dimension $n$ with a Kähler metric $\omega$, and
$dV_{X,\omega} = \omega^n / n!$. Let $(S, h_S)$ be a hermitian holomorphic vector bundle of rank $r
\ge 1$ on $X$ and $\sigma$ a holomorphic section of $S$ transverse to the zero section at every
point of $Y = \sigma^{-1}(0)$, so that $Y$ is a closed submanifold of codimension $r$, and put $\psi
= r \log |\sigma|^2_{h_S}$. Assume that $\psi$ has neat analytic singularities: near every point,
$\psi = r \log \sum_k |g_k|^2 + w$ with holomorphic $g_k$ and smooth $w$. This holds when $S =
L^{\oplus r}$ with the metric induced by a hermitian metric on a line bundle $L$, that is, for $r$
sections $\sigma_1, \dots, \sigma_r$ of $L$ and $|\sigma|^2 = \sum_j |\sigma_j|^2$, but not for
every metric $h_S$ when $r \ge 2$. Then $\psi$ is quasi-plurisubharmonic, its multiplier ideal sheaf
$\mathcal{I}(\psi)$, of germs $f$ with $|f|^2 e^{-\psi}$ locally integrable, is the ideal of $Y$,
and $\mathcal{I}((1 - \varepsilon)\psi) = \mathcal{O}_X$ for $0 < \varepsilon \le 1$: $\psi$ has log
canonical singularities along $Y$. For continuous $g$ with compact support on $Y$ and any continuous
extension $\tilde g$ with compact support on $X$,

$$\int_Y g \, dV_{Y,\omega}[\psi] = \lim_{t \to -\infty} \int_{\{t < \psi < t + 1\}} \tilde g \,
e^{-\psi} dV_{X,\omega}$$

exists and does not depend on $\tilde g$, because the shells shrink to $Y$ with locally uniformly
bounded mass; in Demailly's convention for $|\Lambda^r(d\sigma)|$,

$$dV_{Y,\omega}[\psi] = \frac{2^r \pi^r}{r!} \, |\Lambda^r(d\sigma)|^{-2}_{\omega,h_S} \, dV_{Y,\omega},
\qquad dV_{Y,\omega} = \omega^{n-r}/(n - r)!.$$

Let $\gamma(x) = e^{-x/2}$ for $x \ge 0$ and $\gamma(x) = 1/(1 + x^2)$ for $x \le 0$.

**Theorem** (Demailly, in the transverse case). Let $(E, h)$ be a holomorphic vector bundle on $X$
with a smooth hermitian metric such that $i\Theta_{E,h} + \alpha\, i\partial\bar\partial \psi
\otimes \mathrm{Id}_E$ is Nakano semipositive for all $\alpha \in [1, 1 + \delta]$, for some $\delta >
0$. Then every holomorphic section $f$ of $(K_X \otimes E)|_Y$ with $\int_Y |f|^2_{\omega,h} \,
dV_{Y,\omega}[\psi] < +\infty$ extends to a section $F \in H^0(X, K_X \otimes E)$ with

$$\int_X \gamma(\delta\psi) \, |F|^2_{\omega,h} \, e^{-\psi} \, dV_{X,\omega} \le \frac{34}{\delta}
\int_Y |f|^2_{\omega,h} \, dV_{Y,\omega}[\psi].$$

The constant of the measure is checked on the flat model: for $\sigma(z) = z$ on the unit disc, $r =
n = 1$, $\omega = i\, dz \wedge d\bar z$ and $dV = 2\, dx\, dy$, the shell $\{t < \log |z|^2 < t +
1\}$ has mass $2 \cdot 2\pi \int_{e^{t/2}}^{e^{(t+1)/2}} d\rho/\rho = 2\pi$; in $\mathbb{C}^r$ the
mass is $2^r \pi^r / r!$, and a transverse change of frame contributes the inverse **squared**
Jacobian. Demailly's (2.6) prints the factor $2^{r+1}\pi^r/(r-1)!$, which is $2r$ times this value
and inconsistent with his definition (2.4); Kim and Seo (Lemma 3.5) find the same codimension-one
value, $\pi$ for Lebesgue area, that is $2\pi$ for this $\omega$. Since the printed factor is the
larger, the estimate of the theorem with the printed factor in place of $2^r\pi^r/r!$ is a valid
weaker inequality. For $r = n$, $Y$ is a discrete set of points, and the residual integral $\int_Y
|f|^2_{\omega,h} \, dV_{Y,\omega}[\psi]$ is the sum of the squared values of $f$ divided by the
squared Jacobian determinants of $\sigma$, times $2^n\pi^n/n!$, and a fortiori at most
$2^{n+1}\pi^n/(n-1)!$ times that sum.

The product $|F|^2_{\omega,h} dV_{X,\omega}$ does not depend on $\omega$, any smaller $\delta > 0$
may be used, and the theorem still holds for a line bundle $E$ with a singular metric
$e^{-\varphi}$, the curvature condition becoming $i\partial\bar\partial(\varphi + \alpha \psi) \ge
0$ for $\alpha \in [1, 1 + \delta]$ in the sense of currents (Remarks (2.9)). Demailly proves the
theorem by the twisted $L^2$ estimates for $\bar\partial$ on complete Kähler manifolds, applied on
the complements $X_c \setminus Y$ of $Y$ in the relatively compact sublevel sets $X_c$ of a
plurisubharmonic exhaustion, which carry complete Kähler metrics, together with an approximation of
$\psi$ and the local integrability of the damped density $(1 + |\psi|)^{-(n+1)} |\tilde f|^2
e^{-\psi}$ for a smooth, locally bounded lift $\tilde f$ of the data, which need not vanish on $Y$
(§5, (5.17₂), with Proposition 4.5 (c) for the previous multiplier ideal); the error term from
$\bar\partial$ of the cut-off lift is estimated separately, through a factor that vanishes on $Y$
((5.3)–(5.4)), and Observation 5.1. In the transverse case the first estimate is the finiteness, for
$n \ge 1$, of $\int_0^{1/e} d\rho / (\rho (1 + |\log \rho|)^{n+1})$ in polar coordinates normal to
$Y$, equivalently a computation on the blow-up of $X$ along $Y$.

Demailly states the theorem for every quasi-plurisubharmonic $\psi$ with neat analytic singularities
and log canonical singularities along $Y = V(\mathcal{I}(\psi))$, with the measure on
$Y_{\mathrm{reg}}$ given by the same shell limit (his (2.4)), and states that on a log resolution it
has a smooth positive density at least on a Zariski open subset of $Y_{\mathrm{reg}}$ (Proposition
4.5 (a)); his proof assumes that a single log canonical place lies over the generic point of the
component. Without that assumption the density can fail to exist: by Kim's Theorem 1.2 and
Proposition 4.1, a maximal log canonical centre with at least two log canonical places carries the
infinite measure, while a unique place gives a smooth positive density on a nonempty Zariski open
subset. For $\frac12 \operatorname{div}(y (y - x^2)(y - x)(y + x))$ on a bidisc, blowing up the
origin gives an exceptional divisor of coefficient $1$, and blowing up the common tangent point of
the remaining components, of coefficients $1, \frac12, \frac12$, gives a second one over the same
point. In that generality the shell limit depends on the extension for some test functions supported
in $Y_{\mathrm{reg}}$, so the measure has to be constructed on a resolution. Near a crossing, in a
bidisc with $\psi = \log |zw|^2$ and $Y = \{zw = 0\}$, the zero function on $Y$ has the zero
extension and one equal near the crossing to $(1 + |\log |zw|^2|)^{-1/2}$ off $Y$ and to $0$ on $Y$,
whose shell integrals grow like $|t|^{1/2}$. Even for smooth $Y$: in a bidisc with $\psi = \log
|z|^2 + \log(|z|^2 + |w|^2)$, log canonical with $\mathcal{I}(\psi) = (z)$ and $Y = \{z = 0\}$, the
extension of $0$ by a cut-off times $(1 + |\psi|)^{-1/2}$, set to $0$ on $Y$, has shell integrals
growing at least like $|t|^{1/2}$ (in the chart $z = wu$ of the blow-up of the origin, the shell
contains a strip of area of order $|t|$ in the coordinates $-\log |u|^2$ and $-\log |w|^2$); the
origin is a smaller log canonical centre inside $Y_{\mathrm{reg}}$. A precise general statement,
with the residue measure obtained by push-forward from the log canonical places of a log resolution
and the role of smaller log canonical centres and of maximal centres with several log canonical
places (Kim, Theorems 1.2–1.3 and §3.1), is not part of this page.

## Depends on

- [Nadel vanishing theorem for singular hermitian metrics](nadel-vanishing-for-singular-hermitian-metrics.md),
  for weakly pseudoconvex Kähler manifolds and, in the version for a line bundle with a singular
  metric, singular hermitian metrics
- [Currents of integration and the support theorems](currents-of-integration.md), for the curvature
  condition of that version, in the sense of currents

## Proof depends on

- [L² estimates for the ∂̄ operator](l2-estimates-for-the-dbar-operator.md), for the twisted $L^2$
  estimates on complete Kähler manifolds and the complete Kähler metrics on the complements of $Y$ in
  the sublevel sets of the exhaustion, $Y$ being the zero set of a section of a hermitian vector
  bundle

## Sources

- J.-P. Demailly, "Extension of holomorphic functions defined on non reduced analytic subvarieties"
  (2015): Definitions (2.2)–(2.3), (2.4)–(2.7) and the paragraph after (2.4), pp. 3–4; Theorem (2.8)
  and Remarks (2.9), pp. 4–5; §4 (Proposition 4.5) and the proof of Theorem 2.8 in §5 (Observation
  5.1, (5.3)–(5.4), (5.14)–(5.17) for the constant $34$, and (5.17₂)).
- D. Kim and H. Seo, "On $L^2$ extension from singular hypersurfaces", arXiv:2104.03554 (version 5):
  Definition 3.1, p. 10, and Lemma 3.5, (3.5), p. 13 (the residue measure of a divisor).
- D. Kim, "$L^2$ extension of holomorphic functions for log canonical pairs", arXiv:2108.11934
  (version 3): Theorems 1.2–1.3, pp. 3–4, §3.1, pp. 12–15 (the residue measure on a log resolution),
  and Proposition 4.1 and Remark 4.2, pp. 17–18.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the case $S = L^{\oplus n}$ of a finite set of points defined by $n \ge 1$ sections of a line
  bundle on a compact complex manifold carrying a positive line bundle, with a nonzero Jacobian at
  every zero, the sum of the squared norms of the sections at most $1$, so that $\psi = n \log
  |\sigma|^2 \le 0$, and the curvature condition for every $\alpha \in [1, 1 + \delta]$, with the
  constant $34/\delta$, the weight $\gamma(\delta\psi) e^{-\psi}$ and the constant
  $2^{n+1}\pi^n/(n-1)!$, the weaker bound above, as
  `GlobalTheory.Published.L2ExtensionLogCanonical`.
