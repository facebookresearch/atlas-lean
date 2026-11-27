# Coexistence window in an eco-epidemiological model with Allee effect and prey aggregation

**Model.** Susceptible prey $S$, infected prey $I$ and predators $P$ evolve by

$$\begin{aligned}
\dot S &= a_0 S\Big(1 - \frac{S+I}{K}\Big)(S - L) - d_0 S^r P - e_0 SI,\\
\dot I &= -a_1 I + e_0 SI - d_1 IP,\\
\dot P &= -a_2 P + d_2 S^r P + d_3 IP,
\end{aligned}$$

with all parameters positive, a strong Allee threshold $0 < L < K$, and an aggregation exponent $0 < r < 1$: susceptible prey form herds, so only a sublinear amount $S^r$ is exposed to predation. Infected prey do not reproduce and are caught at rate $d_1 P$.

**Theorem.**
1. Solutions with nonnegative initial data remain nonnegative, and if $d_0 > d_2$ and $d_1 > d_3$, solutions with positive initial data are uniformly bounded.
2. A coexistence equilibrium $E^* = (S^*, I^*, P^*)$ satisfies

$$I^* = \frac{a_2 - d_2 (S^*)^r}{d_3}, \qquad P^* = \frac{e_0 S^* - a_1}{d_1},$$

so both are positive exactly when

$$S_2 := \frac{a_1}{e_0} \;<\; S^* \;<\; S_3 := \Big(\frac{a_2}{d_2}\Big)^{1/r},$$

with $S^*$ a root of the remaining prey equation in this window. The number of such roots depends on the Allee threshold $L$.
3. Varying the Allee threshold $L$, the predator-free equilibrium undergoes a transcritical bifurcation and the coexistence equilibrium undergoes Hopf and saddle-node bifurcations (at the Routh–Hurwitz boundary $\Omega_1\Omega_2 = \Omega_3$, respectively $\Omega_3 = 0$, of its characteristic polynomial $\lambda^3 + \Omega_1\lambda^2 + \Omega_2\lambda + \Omega_3$).

## Expansion

Nonnegativity follows because each right-hand side vanishes on the corresponding coordinate face; boundedness uses a weighted total-biomass Lyapunov function whose decay needs predators to convert less biomass than they consume ($d_2 < d_0$, $d_3 < d_1$). Setting $\dot I = 0$ and $\dot P = 0$ with $I, P > 0$ gives the linear expressions for $P^*$ and $I^*$ in terms of $S^*$, and positivity yields the window. Because $S^r$ has infinite derivative at $0$, the vector field is not Lipschitz on $\{S = 0\}$, which allows extinction in finite time when the Allee effect is strong; small $r$ (strong herding) shields susceptibles and can lower $S$ below $S_2 = a_1/e_0$, where $\dot I < 0$. The source illustrates this for one specific parameter set with a weak Allee effect and initial data converging to a stable coexistence state (its Theorem 6.1 and Figure 6): below a critical exponent $r^* \in (0,1)$ the infected prey go extinct, $I(t) \to 0$. This is an existence statement for that example, observed numerically, not a result for all parameters, and it is not part of the theorem above.

## Sources

- K. Antwi-Fordjour, Z. Overton and D. Lee, "Dynamics of Diseased-Impacted Prey Populations: Defense and Allee Effect Mechanisms", *The European Physical Journal Plus* 140(7) (2025), 675, Theorems 3.1, 3.2, 4.4, 5.1–5.3 and 6.1, <https://doi.org/10.1140/epjp/s13360-025-06611-7> (preprint arXiv:2505.01952).
