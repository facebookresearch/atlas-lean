# Drift prevents predator blow-up in the two-patch additional-food model

**Model.** An AF patch $\Omega_1$ (pest $x_1$, predator $y_1$) and a crop field $\Omega_2$ (pest $x_2$, predator $y_2$) are coupled by one-way predator drift at rate $q_1$ out of $\Omega_1$ that arrives in $\Omega_2$ at rate $q_2$:

$$\begin{aligned}
\dot x_1 &= x_1\left(1 - \frac{x_1}{k_p}\right) - \frac{x_1 y_1}{1 + x_1 + \alpha\xi}, &\quad \dot y_1 &= \epsilon_1\,\frac{x_1 + \xi}{1 + x_1 + \alpha\xi}\, y_1 - \delta_1 y_1 - q_1 y_1,\\
\dot x_2 &= x_2\left(1 - \frac{x_2}{k_c}\right) - \frac{x_2 y_2}{1 + x_2}, &\quad \dot y_2 &= \epsilon_2\,\frac{x_2}{1 + x_2}\, y_2 - \delta_2 y_2 + q_2 y_1,
\end{aligned}$$

where AF of quantity $\xi$ and quality $1/\alpha$ is supplied only in $\Omega_1$, and $\epsilon_i > \delta_i$.

**Theorem.** Let $\xi_{\mathrm{critical}} = \delta_1/(\epsilon_1 - \alpha\delta_1)$.
1. Without drift ($q_1 = q_2 = 0$) and with $\xi > \xi_{\mathrm{critical}}$, the predator population $y_1$ blows up in infinite time.
2. With drift, if $q_1 > 0$ satisfies

$$\max\left(1, \frac{\epsilon_1\xi}{1 + \alpha\xi}\right) < \delta_1 + q_1,$$

then for every $q_2 > 0$ the predator populations remain bounded for all time.

A companion result for symmetric dispersal between the patches gives boundedness whenever $\delta_1 + \delta_2 > \xi/(1 + \alpha\xi) > \delta_1$.

## Expansion

In the single-patch AF model with $\xi > \xi_{\mathrm{critical}}$ the predator nullcline leaves the positive quadrant: the pest goes extinct only as $t \to \infty$, while the AF alone supplies per-capita predator growth $\epsilon_1\xi/(1 + \alpha\xi) - \delta_1 > 0$, so $y_1$ grows without bound. Drift acts as an extra death rate in $\Omega_1$; once $\delta_1 + q_1$ exceeds the maximal AF-supported growth rate, $y_1$ decays, and $y_2$ is a linear equation with a decaying source and a bounded-prey Holling response, hence bounded. In the crop field the pest-free state can then become globally attracting, so pest extinction is achieved without predator explosion.

## Sources

- Urvashi Verma, Aniket Banerjee and Rana D. Parshad, "T(w)o Patch or Not T(w)o Patch: A Novel Biocontrol Model", Mathematical Methods in the Applied Sciences 49 (2026), 14697–14743, <https://doi.org/10.1002/mma.70800>; numbering as in arXiv:2310.17003: Theorem 1 (Section 2.1) and Theorems 4–5 (Section 3.1).
