# Canard explosion and relaxation oscillations in a slow–fast Leslie–Gower model with predator Allee effect

**Model.** Prey $x$ and predator $y$ (dimensionless) with predators reproducing much more slowly than prey:

$$\frac{dx}{dt} = x(1-x) - \frac{\alpha xy}{\beta + x + y} = f(x,y), \qquad \frac{dy}{dt} = \epsilon\, y\Big(\frac{y}{y+\gamma} - \frac{y}{\delta + \theta x}\Big) = \epsilon\, g(x,y),$$

with $\alpha, \beta, \gamma, \delta, \theta > 0$ and $0 < \epsilon \ll 1$. The prey has a ratio-dependent (Beddington–DeAngelis-type) functional response; the predator has a modified Leslie–Gower carrying capacity $\delta + \theta x$ and a weak Allee effect $y/(y+\gamma)$.

**Critical manifold.** For $\epsilon = 0$ the nontrivial prey nullcline is $y = \phi(x) = (1-x)(\beta + x)/(\alpha - 1 + x)$. If $\beta < 1$ and $\alpha > 1/(1-\beta)$, $\phi$ has a local maximum (a generic fold point $Q = (x_m, y_m)$) at

$$x_m = 1 - \alpha + \sqrt{\alpha(\alpha - 1 - \beta)},$$

splitting the curve into an attracting branch $S^a_0$ ($x > x_m$) and a repelling branch $S^r_0$; the prey-free axis $x = 0$ is a second critical manifold, meeting the first at a transcritical point. The interior equilibrium passes through $Q$ when

$$\delta = \delta_* = (\theta + 2)\big(\alpha - \sqrt{\alpha(\alpha - 1 - \beta)} - 1\big) + \gamma - \beta + 1.$$

**Theorem (singular Hopf bifurcation and canard explosion).** Let $D = (\alpha\theta + \delta - \gamma + \beta - \theta - 1)^2 - 4(1+\theta)\big((\alpha - 1)(\delta - \gamma) - \beta\big)$ and consider the parameter regions

$$R_1:\ D > 0,\ \beta < 1,\ \alpha > \tfrac{1}{1-\beta},\ \delta > \gamma + \tfrac{\beta}{\alpha-1},\ \theta(\alpha-1) + \tfrac{\alpha\beta}{\alpha-1} < 1; \qquad R_3:\ \beta < 1,\ \alpha > \tfrac{1}{1-\beta},\ 0 \le \gamma - \delta < 1 \ \text{or}\ \gamma < \delta < \gamma + \tfrac{\beta}{\alpha-1},$$

in which the upper interior equilibrium $E_{2*}$ exists (with a saddle $E_{1*}$ as well in $R_1$). Suppose the parameters at $\delta = \delta_*$ lie in $R_1 \cup R_3$ and the fold is nondegenerate: $\partial_x^2 f(x_m, y_m) = 2\big(\alpha y_m(\beta + y_m)/(\beta + x_m + y_m)^3 - 1\big) \ne 0$. Then for small $\epsilon$:

1. near $\delta = \delta_*$ there is an equilibrium near $Q$, and a singular Hopf bifurcation occurs at $\delta_H(\sqrt\epsilon) = \delta_* + O(\epsilon)$ (explicit first-order coefficient), supercritical or subcritical according to the sign of a first Lyapunov-type coefficient $A$;
2. for each height $s$ of a singular canard cycle (through $Q$, along $S^a_0$ and $S^r_0$ and a fast fiber $y = s$), there is a smooth family of canard cycles at parameter values $\delta(s,\sqrt\epsilon)$ with $|\delta(s,\sqrt\epsilon) - \delta_c(\sqrt\epsilon)| \le e^{-1/\epsilon^K}$, converging to the singular cycle in Hausdorff distance: the small Hopf cycle grows into a large oscillation within an exponentially small $\delta$-window (canard explosion).

**Theorem (relaxation oscillation).** In region $R_3$ with the interior equilibrium to the left of the fold ($x_{2*} < x_m$), for each small $\epsilon > 0$ there is a unique relaxation oscillation $\Gamma_\epsilon$ in a tubular neighborhood of the singular slow–fast cycle (slow drift down the predator axis, fast jump to $S^a_0$, slow drift to $Q$, fast jump back to $x = 0$); it is strictly attracting, with characteristic multiplier bounded by $-K/\epsilon$ for some $K > 0$, and converges to the singular cycle as $\epsilon \to 0$. The paper also proves existence of heteroclinic and homoclinic orbits and bistability between the oscillation and an equilibrium.

## Expansion

Away from the fold, Fenichel theory gives slow manifolds near $S^a_0$ and $S^r_0$. At the fold, blow-up (Krupa–Szmolyan) shows that a canard point arises when the slow nullcline crosses the fold, producing the Hopf and maximal canard curves; along the predator axis, the Entry–Exit (way-in/way-out) function determines where trajectories leave $x = 0$ after a slow passage past the transcritical point. A return map on a transverse section near $Q$ contracts at rate $e^{-c/\epsilon}$, so it has a unique fixed point: the relaxation cycle. Ecologically: when predators are slow, prey crash and recover in bursts, with the switching thresholds set by the hump of the prey nullcline.

## Sources

- Tapan Saha and Pallav Jyoti Pal, "Unveiling the dynamics of canard cycles and global behaviour in a singularly perturbed predator–prey system with Allee effect in predator", Computational and Applied Mathematics 43 (2024), 86, <https://doi.org/10.1007/s40314-024-02603-y>; numbering as in arXiv:2306.13433: model (2), parameter regions $R_1$–$R_4$, the lemmas on the fold point and interior equilibria, and the theorems on singular Hopf bifurcation, canard explosion and relaxation oscillation (sections "Singular Hopf Bifurcation and Canard Cycles" and "Relaxation Oscillation").
