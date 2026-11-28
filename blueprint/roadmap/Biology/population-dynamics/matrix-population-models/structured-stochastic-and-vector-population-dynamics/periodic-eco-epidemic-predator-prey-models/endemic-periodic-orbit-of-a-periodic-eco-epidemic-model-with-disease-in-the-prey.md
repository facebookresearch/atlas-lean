# Endemic periodic orbit of a periodic eco-epidemic model with disease in the prey

**Model.** Susceptible prey $S$, infected prey $I$ and predators $Y$ satisfy

$$S' = \Lambda(t) - \beta(t) S I - \mu(t) S, \qquad I' = \beta(t) S I - c(t) I - \eta(t) Y I, \qquad Y' = Y\big(r(t) - b(t) Y + k(t)\eta(t) I\big),$$

with prey recruitment $\Lambda$, natural prey death $\mu$, incidence $\beta$, death of infected prey $c$, predator intrinsic growth $r$ and self-limitation $b$, predation on infected prey $\eta$ and conversion efficiency $k$. Writing $\overline f = \omega^{-1}\int_0^\omega f(s)\,ds$ for period averages, assume (the source's C1–C2): $\Lambda, \beta, \mu, c, \eta, k$ and $b$ are $\omega$-periodic, non-negative, continuous and bounded; $r$ is $\omega$-periodic, continuous and bounded, of any sign; and $\overline\Lambda, \overline\mu, \overline r, \overline b, \overline\beta > 0$. (That infected prey die faster than susceptible ones, $c > \mu$, is only a modelling remark and is not assumed.) Infected prey do not reproduce and the disease does not pass to predators. Let $s_0(t)$ and $y_0(t)$ be the unique positive $\omega$-periodic solutions of $s' = \Lambda(t) - \mu(t)s$ and $y' = y(r(t) - b(t)y)$. Define

$$\mathcal{R} = \frac{\overline{\beta s_0}}{\overline{c} + \overline{\eta y_0}}.$$

**Theorem.**

1. *(Disease-free orbits.)* The system has exactly two disease-free $\omega$-periodic orbits, $\mathcal{O}_1 = (s_0, 0, 0)$ and $\mathcal{O}_2 = (s_0, 0, y_0)$.
2. *(Extinction.)* If $\mathcal{R} \le 1$, every solution with $Y > 0$ has $\omega$-limit $\mathcal{O}_2$, and every solution with $Y = 0$ has $\omega$-limit $\mathcal{O}_1$.
3. *(Invasion boundary.)* If $\mathcal{R} > 1$, solutions starting with $I = 0$, $Y > 0$ converge to $\mathcal{O}_2$, and those with $I = Y = 0$ converge to $\mathcal{O}_1$.
4. *(Endemic orbit.)* If $\mathcal{R} > 1$, the system has an endemic $\omega$-periodic orbit with $S, I, Y > 0$.

This proves the existence part of the conjecture that permanence of the infected prey yields a globally attracting positive periodic orbit.

## Depends on

- [Threshold dynamics of compartmental epidemic models in periodic environments](../../../../epidemiology/next-generation-matrix-and-the-basic-reproductio/threshold-dynamics-in-periodic-environments.md)

## Expansion

On the disease-free face the equations decouple into the linear periodic equation for $S$ and the periodic logistic equation for $Y$, each with a unique globally attracting positive periodic solution. Linearizing the $I$-equation along $\mathcal{O}_2$ gives $I' = (\beta s_0 - c - \eta y_0) I$, whose Floquet exponent is $\overline{\beta s_0} - \overline c - \overline{\eta y_0}$, positive iff $\mathcal{R} > 1$; for $\mathcal{R} \le 1$ a comparison argument drives $I \to 0$ and the asymptotically periodic reduced system then converges to the disease-free orbit. For the endemic orbit, substitute $S = e^{u_1}$, $I = e^{u_2}$, $Y = e^{u_3}$ and apply Mawhin's continuation theorem: the operator $u \mapsto u'$ on $\omega$-periodic functions is Fredholm of index zero, a priori bounds on solutions of the homotopy $u' = \lambda N(u)$ built from period averages and $\mathcal{R} > 1$ define a bounded open set avoiding solutions on its boundary, and the Brouwer degree of the averaged vector field on the kernel (constants) is nonzero.

## Sources

- César M. Silva, "Existence of periodic solutions for periodic eco-epidemic models with disease in the prey", Journal of Mathematical Analysis and Applications 453 (2017), 383–397, <https://doi.org/10.1016/j.jmaa.2017.03.074>. Published version of arXiv:1601.05125, cited next; locators there refer to the arXiv version.
- César M. Silva, "Existence of periodic orbits for periodic eco-epidemic models with disease in the prey", arXiv (2016). Theorems 1–5, Definitions 1–2. <https://doi.org/10.48550/arXiv.1601.05125>
