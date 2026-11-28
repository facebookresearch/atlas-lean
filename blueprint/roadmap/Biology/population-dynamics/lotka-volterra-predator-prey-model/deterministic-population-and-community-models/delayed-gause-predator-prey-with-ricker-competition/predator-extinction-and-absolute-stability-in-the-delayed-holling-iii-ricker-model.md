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
4. Suppose $\gamma K^2/(a^2 + K^2) > \beta$, so that a positive equilibrium exists, and let $(x_*, y_*)$ be one. Its characteristic equation is $\lambda^2 + m\lambda + n\lambda e^{-\lambda\tau} + p + qe^{-\lambda\tau} = 0$ with

$$m = r\Big(1 - \frac{x_*}{K}\Big)\Big(\frac{2a^2}{a^2 + x_*^2} - 1\Big) + \beta + \frac{rx_*}{K},\quad n = \beta\Big(\frac{y_*}{N} - 1\Big),\quad p = -\beta(\beta - m),\quad q = -\beta r\Big(1 - \frac{2x_*}{K}\Big).$$

Assume

$$\text{(H2)}\ \ \frac{rx_*/K + \beta y_*/N}{r(1 - x_*/K)} > 1 - \frac{2a^2}{a^2 + x_*^2}, \qquad \text{(H3)}\ \ \frac{\gamma x_*y_*a^2}{(a^2 + x_*^2)^2} > r\Big(1 - \frac{2x_*}{K}\Big).$$

   a) If $2p + n^2 - m^2 < 0$, then $(x_*, y_*)$ is locally absolutely stable.

   b) If $2p + n^2 - m^2 > 2\sqrt{p^2 - q^2}$, let $\omega_\pm^2 = \tfrac12\big[(n^2 - m^2 + 2p) \pm \sqrt{(n^2 - m^2 + 2p)^2 - 4(p^2 - q^2)}\big]$ and

$$\tau_j^\pm = \frac{1}{\omega_\pm}\arccos\frac{q(\omega_\pm^2 - p) - mn\omega_\pm^2}{q^2 + n^2\omega_\pm^2} + \frac{2\pi j}{\omega_\pm},\qquad j = 0, 1, 2, \dots$$

   Then there is a positive integer $k$ such that $(x_*, y_*)$ is asymptotically stable for $\tau \in [0, \tau_0^+) \cup (\tau_0^-, \tau_1^+) \cup \dots \cup (\tau_{k-1}^-, \tau_k^+)$ and unstable for $\tau \in [\tau_0^+, \tau_0^-) \cup [\tau_1^+, \tau_1^-) \cup \dots \cup [\tau_{k-1}^+, \tau_{k-1}^-) \cup (\tau_k^+, \infty)$: finitely many stability switches, ending in predator–prey oscillations.

## Proof sketch

Item 3 is a comparison argument: the per-capita predator birth term is at most $\gamma\,x^2/(a^2+x^2)\,e^{-y/N} < \gamma$, so if $\beta > \gamma$ the predator equation is dominated by a linear delay equation $\dot z = -\beta z + \gamma z(t-\tau)$, whose solutions decay for all $\tau$ because $\beta > \gamma$; then the prey equation is asymptotically logistic and $x \to K$. Item 2 linearizes at $(K, 0)$: the prey direction gives the eigenvalue $-r$, and the predator direction gives $\lambda = -\beta + \frac{\gamma K^2}{a^2+K^2}e^{-\lambda\tau}$, all of whose roots have negative real part for every $\tau$ when $\beta > \gamma K^2/(a^2+K^2)$. For item 4, (H2) gives $m + n > 0$ and (H3) gives $p + q > 0$, while $p - q = 2\beta\gamma x_*y_*a^2/(a^2 + x_*^2)^2 > 0$. Substituting $\lambda = i\omega$ and separating real and imaginary parts gives $\omega^4 + (m^2 - n^2 - 2p)\omega^2 + p^2 - q^2 = 0$, whose positive roots $\omega_\pm$ define the crossing delays $\tau_j^\pm$; the Cooke–Grossman theorem then gives a) when no root exists and b) when two do.

## Sources

- Wilson Mejías and Daniel Sepúlveda, "Stability of a Delayed Predator-Prey Model for Puma Concolor", *Differential Equations and Dynamical Systems* (2025), <https://doi.org/10.1007/s12591-025-00745-x>. Preprint version: arXiv:2407.07904 (2024), model equations, existence theorem, absolute-stability definition, the theorems on $(K,0)$ and predator extinction, and the positive-equilibrium stability theorem based on the Cooke–Grossman proposition, <https://doi.org/10.48550/arXiv.2407.07904>.
