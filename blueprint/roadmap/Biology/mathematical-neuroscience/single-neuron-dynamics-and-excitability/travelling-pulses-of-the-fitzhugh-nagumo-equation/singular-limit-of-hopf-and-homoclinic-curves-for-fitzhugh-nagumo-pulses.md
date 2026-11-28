# Singular limit of Hopf and homoclinic bifurcation curves for FitzHugh–Nagumo travelling pulses

**Setting.** For the FitzHugh–Nagumo nerve-conduction equation $u_\tau = \delta u_{xx} + f_a(u) - w + p$, $w_\tau = \epsilon(u - \gamma w)$ with $f_a(u) = u(u-a)(1-u)$, travelling waves $u(x + s\tau)$ with speed $s$ solve a three-dimensional fast–slow ODE. With $a = \frac1{10}$, $\delta = 5$, $\gamma = 1$ and the slow time rescaled, it reads

$$\epsilon\dot x_1 = x_2, \qquad \epsilon\dot x_2 = \tfrac15\big(s x_2 - f(x_1) + y - p\big), \qquad \dot y = \tfrac1s(x_1 - y),$$

with $f(x_1) = x_1(x_1 - 1)(\tfrac1{10} - x_1)$. Homoclinic orbits correspond to travelling pulses, and in the $(p, s)$ parameter plane the system has a C-shaped curve of homoclinic bifurcations and a U-shaped curve of Hopf bifurcations of the equilibrium. The critical curve $C_0 = \{x_2 = 0,\ y = c(x_1)\}$ has fold points at $x_{1,\pm} = \frac{1}{30}\big(11 \pm \sqrt{91}\big)$, i.e. $x_{1,+} \approx 0.6846$, $x_{1,-} \approx 0.0487$.

**Proposition (singular limit, $\epsilon \to 0$).**
1. *Hopf curve.* The U-shaped Hopf curves have vertical asymptotes $p = p_- \approx 0.0510636$ and $p = p_+ \approx 0.558418$ and the horizontal asymptote $\{(p, s): p \in [p_-, p_+],\ s = 0\}$; at $p_\pm$ the equilibrium passes through the fold points.
2. *Fast heteroclinics.* For $s = 0$ the fast subsystem has a double heteroclinic connection at $\bar p = \bar p^* \approx -0.0619259$, and for each $y_0$ one at $p = \bar p^* + y_0$ in the plane $y = y_0$. The full system has a singular double heteroclinic connection for $s = 0$ at $p = p^* \approx -0.246016$.
3. *Homoclinic curve.* The singular homoclinic curve for positive wave speed ends at $(p, s) = (p_-, s^*)$ with $s^* \approx 1.50815$ on the right and at $(p^*, 0)$ on the left.
4. *Canards.* Near the fold point $(x_{1,-}, c(x_{1,-}))$ of the two-slow/one-fast reduction, the maximal canard lies on $p(\epsilon) = x_{1,-} - c(x_{1,-}) + \frac58\epsilon + O(\epsilon^{3/2})$, and the canard cycles born there are stable.

**Conjecture.** With $A = (p^*, 0)$, $B = (p_-, 0)$ and $C = (p_-, s^*)$, the C-shaped homoclinic bifurcation curves converge as $\epsilon \to 0$ to the union of the segments $AB$ and $AC$ (supported by continuation for $\epsilon$ down to $5 \cdot 10^{-5}$).

## Proof sketch

At $\epsilon = 0$ the dynamics splits into a fast subsystem in $(x_1, x_2)$ with $y$ frozen and a slow flow on the critical curve $C_0$. A travelling pulse is approximated by a singular orbit: a fast front from the left to the right branch of $C_0$, slow drift along it, a fast back, and slow return. The fast front and back exist exactly when the cubic nullcline admits heteroclinic connections at the given $s$, which produces the explicit endpoints; the Hopf asymptotes come from the equilibrium crossing the folds, where the slow flow degenerates. Numerical continuation for small $\epsilon$ matches these singular predictions. The canard formula is the generic fold-point expansion for planar slow–fast systems.

## Sources

- John Guckenheimer and Christian Kuehn, "Homoclinic orbits of the FitzHugh-Nagumo equation: The singular-limit", *Discrete and Continuous Dynamical Systems - S* 2 (2009), 851–872, <https://doi.org/10.3934/dcdss.2009.2.851>. Preprint version: arXiv:1201.5901 (2012), Section 1.2 (travelling-wave system), Section 2 (fold points, Propositions 1–4), Section 3 (Propositions 5–7 and Conjecture 1), <https://doi.org/10.48550/arXiv.1201.5901>.
