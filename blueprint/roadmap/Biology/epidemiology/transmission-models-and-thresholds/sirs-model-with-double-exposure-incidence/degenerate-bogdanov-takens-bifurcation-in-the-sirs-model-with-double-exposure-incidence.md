# Degenerate Bogdanov–Takens bifurcation in the SIRS model with double-exposure incidence

**Model.** In a single isolated population with recruitment $b > 0$, natural death rate $d > 0$, recovery rate $\alpha > 0$ and loss-of-immunity rate $\gamma_R > 0$, let the incidence be $\beta(1 + \nu I) I S$ with $\beta > 0$ and $\nu \ge 0$: $\beta I S$ counts infections from single contacts and $\beta\nu I^2 S$ infections requiring a double exposure. The SIRS system

$$\dot S = b - dS - \beta(1+\nu I) I S + \gamma_R R, \qquad \dot I = \beta(1+\nu I)IS - (d+\alpha) I, \qquad \dot R = \alpha I - (d+\gamma_R) R$$

has the attracting invariant plane $S + I + R = b/d$. On it, after the rescaling $I \mapsto \beta I/(d+\gamma_R)$, $R \mapsto \beta R/(d+\gamma_R)$, $t \mapsto (d+\gamma_R)t$, the dynamics are

$$\dot I = I(1 + pI)(A - I - R) - \frac{A}{\mathcal R_0} I, \qquad \dot R = qI - R,$$

with

$$p = \frac{\nu(d+\gamma_R)}{\beta}, \quad A = \frac{b\beta}{d(d+\gamma_R)}, \quad \mathcal R_0 = \frac{b\beta}{d(d+\alpha)}, \quad q = \frac{\alpha}{d+\gamma_R}, \qquad q\mathcal R_0 < A < (q+1)\mathcal R_0 .$$

**Equilibria.** Positive equilibria have $R = qI$ with $I \in (0, A)$ a root of $p(q+1)I^2 + (1 + q - Ap)I + A/\mathcal R_0 - A = 0$. Put

$$\mathcal R_0^* = \frac{4Ap(1+q)}{(1+q+Ap)^2} \le 1 .$$

Then: if $\mathcal R_0 \le 1$ and $p \le (1+q)/A$, or $\mathcal R_0 < \mathcal R_0^*$ and $p > (1+q)/A$, the disease-free equilibrium $E_0$ is the only equilibrium and is globally asymptotically stable; if $\mathcal R_0 > 1$ and $p \le 1/A$, there is a unique endemic equilibrium and it is globally asymptotically stable; if $\mathcal R_0^* < \mathcal R_0 < 1$ and $p > (1+q)/A$, $E_0$ is stable and coexists with a saddle $E_-$ and an anti-saddle $E_+$ (backward bifurcation).

**Theorem (cusp).** Let $\mathcal R_0 = \mathcal R_0^*$ and $p > (1+q)/A$, so that $E_\pm$ merge into a unique positive equilibrium $E^*$. Set

$$A^* = \frac{(q+1)\sqrt{4p+q}}{p\sqrt q}, \qquad p^* = \frac{q^3 + 2q^2}{4}.$$

Then $E^*$ is a saddle-node with a stable parabolic sector if $A < A^*$ and an unstable one if $A > A^*$. If $A = A^*$, $E^*$ is a cusp of codimension $2$ when $p \ne p^*$ and a cusp of codimension $3$ when $p = p^*$.

**Theorem (unfolding).** As $(\mathcal R_0, A, p)$ vary near $(\mathcal R_0^*, A^*, p^*)$, the system undergoes a degenerate Bogdanov–Takens bifurcation of codimension $3$ (cusp case), fully unfolded within the model. The codimension-3 cusp organizes the bifurcation set: saddle-node, Hopf, homoclinic and double-limit-cycle bifurcations (codimension 1); Bogdanov–Takens, degenerate Hopf, degenerate homoclinic and simultaneous Hopf–homoclinic bifurcations (codimension 2). In particular, two limit cycles can be born in a codimension-2 Hopf bifurcation and disappear in a codimension-2 homoclinic bifurcation.

## Expansion

$\mathcal R_0^*$ is the value of $\mathcal R_0$ at which the discriminant of the endemic quadratic vanishes, so $\Delta \ge 0$ iff $\mathcal R_0 \ge \mathcal R_0^*$. At the double root the Jacobian has zero determinant, and the shift $I = (X + Y)/q + I^*$, $R = X + R^*$ brings the system to $\dot X = Y$, $\dot Y = \sum_{2 \le i+j \le 3} a_{ij}X^iY^j$ with $a_{20} < 0$ always. A near-identity change of variables gives the normal form $\dot x = y$, $\dot y = b_{20}x^2 + b_{11}xy + \dots$ with

$$b_{11} = 1 + \frac1q - \frac{\sqrt{4p+q}}{q^{3/2}},$$

which vanishes exactly when $4p + q = q(q+1)^2$, that is $p = p^*$; then the next normal-form coefficient (of $x^3 y$) is nonzero, so the cusp has codimension exactly $3$. For the unfolding, a sequence of near-identity transformations and time rescalings reduces the three-parameter family to $\dot x_1 = y_1$, $\dot y_1 = \gamma_1 + \gamma_2 y_1 + \gamma_3 x_1 y_1 + x_1^2 + x_1^3 y_1 + \dots$, and the Jacobian $\partial(\gamma_1,\gamma_2,\gamma_3)/\partial(\mathcal R_0, A, p)$ at the cusp is nonzero for every $q > 0$, which is the versality condition of the Dumortier–Roussarie–Sotomayor theory. Epidemiologically, double exposures ($p > 0$ large enough) make disease persistence depend on the initial state: depending on parameters the population can tend to $E_0$, to an endemic equilibrium or to sustained periodic outbreaks, with several such attractors coexisting.

## Sources

- M. Lu, D. Gao, J. Huang, H. Wang, "Relative prevalence-based dispersal in an epidemic patch model", *Journal of Mathematical Biology* 86 (2023), Lemma 2.1, Eqs. (2.2)–(2.11), Table 1, Remark 2.3, Theorems 2.5 and 2.7. <https://doi.org/10.1007/s00285-023-01887-8> (PMC9987411).
- P. van den Driessche, J. Watmough, "A simple SIS epidemic model with a backward bifurcation", *Journal of Mathematical Biology* 40 (2000) 525–540 (origin of the double-exposure incidence). <https://doi.org/10.1007/s002850000032>.
