# L² extension from subvarieties defined by log canonical weights

Let $X$ be a weakly pseudoconvex Kähler manifold of dimension $n$ with a Kähler metric $\omega$, and
$dV_{X,\omega} = \omega^n / n!$. Let $\psi \colon X \to [-\infty, +\infty)$ be a quasi-plurisubharmonic
function with neat analytic singularities: near every point $\psi = c \log \sum_k |g_k|^2 + w$ with
$c \ge 0$, holomorphic $g_k$ and smooth $w$. Let $\mathcal{I}(\psi)$ be its multiplier ideal sheaf, of
germs $f$ with $|f|^2 e^{-\psi}$ locally integrable, and $Y = V(\mathcal{I}(\psi))$; assume that $\psi$
has log canonical singularities along $Y$, that is, $\mathcal{I}((1 - \varepsilon)\psi)|_Y =
\mathcal{O}_X|_Y$ for every $\varepsilon > 0$, so that $Y$ is reduced. On $Y^\circ = Y_{\mathrm{reg}}$ let
$dV_{Y^\circ,\omega}[\psi]$ be the measure with
$$\int_{Y^\circ} g \, dV_{Y^\circ,\omega}[\psi] = \limsup_{t \to -\infty} \int_{\{t < \psi < t + 1\}}
\tilde g \, e^{-\psi} dV_{X,\omega}$$
for continuous compactly supported $g$ on $Y^\circ$ with a continuous compactly supported extension
$\tilde g$, and let $\gamma(x) = e^{-x/2}$ for $x \ge 0$, $\gamma(x) = 1/(1 + x^2)$ for $x \le 0$.

**Theorem** (Demailly). Let $(E, h)$ be a holomorphic vector bundle on $X$ with a smooth hermitian
metric such that $i\Theta_{E,h} + \alpha\, i\partial\bar\partial \psi \otimes \mathrm{Id}_E$ is Nakano
semipositive for all $\alpha \in [1, 1 + \delta]$, for some $\delta > 0$. Then every holomorphic section
$f$ of $(K_X \otimes E)|_{Y^\circ}$ with $\int_{Y^\circ} |f|^2_{\omega,h} \, dV_{Y^\circ,\omega}[\psi] <
+\infty$ extends to a section $F \in H^0(X, K_X \otimes E)$ with
$$\int_X \gamma(\delta\psi) \, |F|^2_{\omega,h} \, e^{-\psi} \, dV_{X,\omega} \le \frac{34}{\delta}
\int_{Y^\circ} |f|^2_{\omega,h} \, dV_{Y^\circ,\omega}[\psi].$$

If $Y$ is a subvariety of codimension $r$ defined by a section $\sigma$ of a hermitian vector bundle
$(S, h_S)$, generically transverse to the zero section along $Y$, and $\psi = r \log |\sigma|^2_{h_S}$,
then $dV_{Y^\circ,\omega}[\psi] = \frac{2^{r+1} \pi^r}{(r - 1)!} \, |\Lambda^r(d\sigma)|^{-2}_{\omega,h_S}
\, dV_{Y,\omega}$ with $dV_{Y,\omega} = \omega^{n-r}/(n - r)!$ on $Y^\circ$. For $r = n$ and $Y$ a finite
set of points the right-hand side is a finite sum of the squared values of $f$ divided by the squared
Jacobian determinants of $\sigma$, times $2^{n+1}\pi^n/(n-1)!$. The product $|F|^2_{\omega,h}
dV_{X,\omega}$ does not depend on $\omega$, and the theorem still holds for a line bundle $E$ with a
singular metric $e^{-\varphi}$, the curvature condition becoming $i\partial\bar\partial(\varphi + \alpha
\psi) \ge 0$ for $\alpha \in [1, 1 + \delta]$ in the sense of currents. Demailly proves the theorem by
the twisted $L^2$ estimates for $\bar\partial$ on complete Kähler manifolds, with an approximation of
$\psi$ and Hironaka's resolution for the neat analytic singularities.

## Proof depends on

- [L² estimates for the ∂̄ operator](l2-estimates-for-the-dbar-operator.md), for the twisted $L^2$
  estimates on complete Kähler manifolds
- [Resolution of singularities of quasi-projective varieties](resolution-of-singularities-of-quasi-projective-varieties.md),
  for the measure $dV_{Y^\circ,\omega}[\psi]$ and the log canonical weights with neat analytic
  singularities

## Sources

- J.-P. Demailly, "Extension of holomorphic functions defined on non reduced analytic subvarieties"
  (2015): Definitions (2.2)–(2.3), (2.4)–(2.7),
  pp. 3–4; Theorem (2.8) and Remarks (2.9), pp. 4–5; the proof of Theorem 2.8 in §5.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses the case of a finite set of points defined by $n$ sections of a line
  bundle on a compact complex manifold carrying a positive line bundle, with $\psi = n \log |\sigma|^2$,
  the constant $34/\delta$, the weight $\gamma(\delta\psi) e^{-\psi}$ and the residue measure above, as
  `GlobalTheory.Published.L2ExtensionLogCanonical`.
