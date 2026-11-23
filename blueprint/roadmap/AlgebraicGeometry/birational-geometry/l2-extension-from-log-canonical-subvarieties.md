# L² extension from subvarieties defined by log canonical weights

Let $X$ be a weakly pseudoconvex Kähler manifold of dimension $n$ with a Kähler metric $\omega$, and
$dV_{X,\omega} = \omega^n / n!$. Let $\psi \colon X \to [-\infty, +\infty)$ be a
quasi-plurisubharmonic function with neat analytic singularities: near every point $\psi = c \log
\sum_k |g_k|^2 + w$ with $c \ge 0$, holomorphic $g_k$ and smooth $w$. Let $\mathcal{I}(\psi)$ be its
multiplier ideal sheaf, of germs $f$ with $|f|^2 e^{-\psi}$ locally integrable, and $Y =
V(\mathcal{I}(\psi))$; assume that $\psi$ has log canonical singularities along $Y$, that is,
$\mathcal{I}((1 - \varepsilon)\psi)|_Y = \mathcal{O}_X|_Y$ for every $\varepsilon > 0$, so that $Y$
is reduced. On $Y^\circ = Y_{\mathrm{reg}}$ let $dV_{Y^\circ,\omega}[\psi]$ be the measure with
$$\int_{Y^\circ} g \, dV_{Y^\circ,\omega}[\psi] = \limsup_{t \to -\infty} \int_{\{t < \psi < t + 1\}}
\tilde g \, e^{-\psi} dV_{X,\omega}$$
for continuous $g$ with compact support in $Y^\circ$ and a continuous extension $\tilde g$ with
compact support in $X \setminus (Y \setminus Y^\circ)$, away from the singular locus of $Y$; the
value does not depend on such an extension, and the measure is extended by zero to $Y$. Extensions
that meet the singular locus must be excluded: in a bidisc with $\psi = \log |zw|^2$ and $Y = \{zw =
0\}$, take $g = 0$ on $Y^\circ$ and an extension equal near the crossing to $(1 + |\log
|zw|^2|)^{-1/2}$ off $Y$ and to $0$ on $Y$; it is continuous, but its shell integrals grow like
$|t|^{1/2}$. Let $\gamma(x) = e^{-x/2}$ for $x \ge 0$ and $\gamma(x) = 1/(1 + x^2)$ for $x \le 0$.

**Theorem** (Demailly). Let $(E, h)$ be a holomorphic vector bundle on $X$ with a smooth hermitian
metric such that $i\Theta_{E,h} + \alpha\, i\partial\bar\partial \psi \otimes \mathrm{Id}_E$ is
Nakano semipositive for all $\alpha \in [1, 1 + \delta]$, for some $\delta > 0$. Then every
holomorphic section $f$ of $(K_X \otimes E)|_{Y^\circ}$ with $\int_{Y^\circ} |f|^2_{\omega,h} \,
dV_{Y^\circ,\omega}[\psi] < +\infty$ extends to a section $F \in H^0(X, K_X \otimes E)$ with
$$\int_X \gamma(\delta\psi) \, |F|^2_{\omega,h} \, e^{-\psi} \, dV_{X,\omega} \le \frac{34}{\delta}
\int_{Y^\circ} |f|^2_{\omega,h} \, dV_{Y^\circ,\omega}[\psi].$$

If $Y$ is a subvariety of codimension $r$ defined by a section $\sigma$ of a hermitian vector bundle
$(S, h_S)$, generically transverse to the zero section along $Y$, and $\psi = r \log
|\sigma|^2_{h_S}$, then the definition gives, in Demailly's convention for $|\Lambda^r(d\sigma)|$,
$$dV_{Y^\circ,\omega}[\psi] = \frac{2^r \pi^r}{r!} \, |\Lambda^r(d\sigma)|^{-2}_{\omega,h_S} \,
dV_{Y,\omega}, \qquad dV_{Y,\omega} = \omega^{n-r}/(n - r)! \text{ on } Y^\circ.$$
The constant is checked on the flat model: for $\sigma(z) = z$ on the unit disc, $r = n = 1$,
$\omega = i\, dz \wedge d\bar z$ and $dV = 2\, dx\, dy$, the shell $\{t < \log |z|^2 < t + 1\}$ has
mass $2 \cdot 2\pi \int_{e^{t/2}}^{e^{(t+1)/2}} d\rho/\rho = 2\pi$; in $\mathbb{C}^r$ the mass is
$2^r \pi^r / r!$, and a transverse change of frame contributes the inverse **squared** Jacobian.
Demailly's (2.6) prints the factor $2^{r+1}\pi^r/(r-1)!$, which is $2r$ times this value and
inconsistent with his definition (2.4); Kim and Seo (Lemma 3.5) find the same codimension-one value,
$\pi$ for Lebesgue area, that is $2\pi$ for this $\omega$. Since the printed factor is the larger,
the estimate of the theorem with the printed factor in place of $2^r\pi^r/r!$ is a valid weaker
inequality. For $r = n$ and $Y$ a finite set of points the right-hand side is a finite sum of the
squared values of $f$ divided by the squared Jacobian determinants of $\sigma$, times $2^n\pi^n/n!$,
and a fortiori at most $2^{n+1}\pi^n/(n-1)!$ times that sum.

The product $|F|^2_{\omega,h} dV_{X,\omega}$ does not depend on $\omega$, any smaller $\delta > 0$
may be used, and the theorem still holds for a line bundle $E$ with a singular metric
$e^{-\varphi}$, the curvature condition becoming $i\partial\bar\partial(\varphi + \alpha \psi) \ge
0$ for $\alpha \in [1, 1 + \delta]$ in the sense of currents (Remarks (2.9)). Demailly proves the
theorem by the twisted $L^2$ estimates for $\bar\partial$ on complete Kähler manifolds, applied on
the complement of the polar set of $\psi$, which carries a complete Kähler metric, after a
principalization of the coherent analytic ideal defining the singularities of $\psi$ (with control
of the exceptional and Jacobian divisors and the change of variables), and an approximation of
$\psi$ (§§4–5, Proposition 4.5 (c), Observation 5.1).

## Proof depends on

- [L² estimates for the ∂̄ operator](l2-estimates-for-the-dbar-operator.md), for the twisted $L^2$
  estimates on complete Kähler manifolds and the complete Kähler metrics on complements of analytic
  subsets
- [Principalization relative to a simple normal crossing divisor](resolution-of-singularities/principalization-relative-to-a-simple-normal-crossing-divisor.md),
  in its analytic form, for the coherent analytic ideal defining the singularities of $\psi$

## Sources

- J.-P. Demailly, "Extension of holomorphic functions defined on non reduced analytic subvarieties"
  (2015): Definitions (2.2)–(2.3), (2.4)–(2.7), pp. 3–4; Theorem (2.8) and Remarks (2.9), pp. 4–5;
  §4 (Proposition 4.5) and the proof of Theorem 2.8 in §5 (Observation 5.1, (5.14)–(5.17) for the
  constant $34$).
- D. Kim and H. Seo, "On $L^2$ extension from singular hypersurfaces", arXiv:2104.03554 (version 5):
  Definition 3.1, p. 10, and Lemma 3.5, (3.5), p. 13 (the residue measure of a divisor).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the case of a finite set of points defined by $n \ge 1$ sections of a line bundle on a
  compact complex manifold carrying a positive line bundle, with a nonzero Jacobian at every zero,
  the sum of the squared norms of the sections at most $1$, so that $\psi = n \log |\sigma|^2 \le
  0$, and the curvature condition for every $\alpha \in [1, 1 + \delta]$, with the constant
  $34/\delta$, the weight $\gamma(\delta\psi) e^{-\psi}$ and the constant $2^{n+1}\pi^n/(n-1)!$, the
  weaker bound above, as `GlobalTheory.Published.L2ExtensionLogCanonical`.
