# Predator extinction and absolute stability in the delayed Holling III–Ricker model

**Model.** Prey $x(t)$ and predators $y(t)$ (for example deer and pumas) satisfy

$$\begin{aligned}
\dot x(t) &= r\Big(1 - \frac{x(t)}{K}\Big)x(t) - \frac{\gamma x(t)^2}{a^2 + x(t)^2}\,y(t),\\
\dot y(t) &= -\beta y(t) + \frac{\gamma x(t-\tau)^2}{a^2 + x(t-\tau)^2}\,y(t-\tau)\,e^{-y(t-\tau)/N},
\end{aligned}$$

with logistic prey growth (rate $r$, carrying capacity $K$), a Holling type III functional response (maximal rate $\gamma$, half-saturation $a$), predator mortality $\beta$, a maturation or gestation delay $\tau \ge 0$, and a Ricker factor $e^{-y/N}$ for intraspecific competition among predators. Initial data are non-negative continuous functions on $[-\tau, 0]$.

An equilibrium is *absolutely stable* if it is asymptotically stable for every delay $\tau \ge 0$, and *conditionally stable* if this holds only for $\tau$ in some interval.

**Theorem.**
1. For every non-negative initial function the system has a unique non-negative solution on $[-\tau, \infty)$.
2. If $\beta > \gamma K^2/(a^2 + K^2)$, the predator-free equilibrium $(K, 0)$ is locally absolutely stable.
3. If $\beta > \gamma$, every solution with positive initial data converges to $(K, 0)$: predators go extinct for every delay.
4. At a positive equilibrium $(x_*, y_*)$, under explicit inequalities on $r, K, a, \gamma, \beta, N$ evaluated at $(x_*,y_*)$, the characteristic equation $\lambda^2 + p\lambda + q + (s\lambda + m)e^{-\lambda\tau} = 0$ either has all roots in the left half-plane for all $\tau$ (absolute stability) or loses stability at the first critical delay $\tau_0^+$ given by the Cooke–Grossman crossing formulas, where a pair of characteristic roots crosses the imaginary axis (a stability switch toward predator–prey oscillations).

## Proof sketch

Item 3 is a comparison argument: the per-capita predator birth term is at most $\gamma\,x^2/(a^2+x^2)\,e^{-y/N} < \gamma$, so if $\beta > \gamma$ the predator equation is dominated by a linear delay equation $\dot z = -\beta z + \gamma z(t-\tau)$, whose solutions decay for all $\tau$ because $\beta > \gamma$; then the prey equation is asymptotically logistic and $x \to K$. Item 2 linearizes at $(K, 0)$: the prey direction gives the eigenvalue $-r$, and the predator direction gives $\lambda = -\beta + \frac{\gamma K^2}{a^2+K^2}e^{-\lambda\tau}$, all of whose roots have negative real part for every $\tau$ when $\beta > \gamma K^2/(a^2+K^2)$. For item 4, substituting $\lambda = i\omega$ and separating real and imaginary parts gives a quartic in $\omega$ whose positive roots define the crossing delays $\tau_j^\pm$ (Cooke–Grossman).

## Sources

- Wilson Mejías and Daniel Sepúlveda, "Stability of a Delayed Predator-Prey Model for Puma Concolor", *Differential Equations and Dynamical Systems* (2025), <https://doi.org/10.1007/s12591-025-00745-x>. Preprint version: arXiv:2407.07904 (2024), model equations, existence theorem, absolute-stability definition, the theorems on $(K,0)$ and predator extinction, and the positive-equilibrium stability theorem based on the Cooke–Grossman proposition, <https://doi.org/10.48550/arXiv.2407.07904>.
