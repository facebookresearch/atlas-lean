# Equal growth rates reduce a two-strategy density game to a time-rescaled replicator equation

Consider the density game with $n = 2$ strategies, equal growth rates $r_1 = r_2 = r > 0$ and positive payoff matrix $A = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$, so that $K_1 = a y_1 + b y_2$ and $K_2 = c y_1 + d y_2$ with $y_i = x_i / x_T$.

**Theorem.** In this case the strategy frequencies satisfy

$$\dot y_1 = y_1 y_2\, (K_1 - K_2)\, C_1, \qquad C_1 = \frac{r\, x_T}{K_1 K_2} > 0,$$

which is the replicator equation $\dot y_1 = y_1 y_2 (K_1 - K_2)$ with time rescaled by the positive factor $C_1$. Consequently the equilibria, their frequencies and their stability, including the interior equilibrium, coincide with those of the replicator equation. Explicitly, if $a \ne c$, $d \ne b$ and $\operatorname{sgn}(a - c) = \operatorname{sgn}(d - b)$, the interior equilibrium is

$$\hat x_1 = \frac{(d - b)(ad - bc)}{(a - c + d - b)^2}, \qquad \hat x_2 = \frac{(a - c)(ad - bc)}{(a - c + d - b)^2}, \qquad \hat x_T = \frac{ad - bc}{a - c + d - b},$$

with $\hat y_1 = (d - b)/(a - c + d - b)$. It is a global attractor if $a < c$ and $d < b$ (coexistence, e.g. Hawk–Dove), and the system is bistable if $a > c$ and $d > b$ (e.g. Stag Hunt).

## Proof sketch

With $r_1 = r_2$, the per-capita growth rates of the two strategies are $r(1 - x_T/K_1)$ and $r(1 - x_T/K_2)$; their difference is $r x_T (K_1 - K_2)/(K_1 K_2)$, and $\dot y_1 = y_1 y_2 \times$ (difference of per-capita rates) gives the formula. The rescaling factor depends on the total density $x_T$ only through a positive speed, so the frequency dynamics has the phase portrait of the replicator equation. The ray $x_2 / x_1 = (a - c)/(d - b)$ through the origin and the interior equilibrium is invariant, which excludes limit cycles and makes the attractor global. The ecological component $\dot x_T = x_T \sum_i r y_i (1 - x_T/K_i)$ does not affect the frequency dynamics. With unequal growth rates this reduction fails: the sign of $\dot y_1$ can change along rays $x_2 = \kappa x_1$, so the frequency dynamics depends on absolute density.

## Depends on

- [Equilibria and monomorphic stability of density games coincide with the replicator equation](density-game-equilibria-coincide-with-replicator-dynamics.md)
- [Solution of the replicator equation](../../../replicator-dynamics/is-solution.md)

## Sources

- S. Novak, K. Chatterjee and M. A. Nowak, "Density games", *Journal of Theoretical Biology* (2013), Section 3, Eq. (5) and Theorem 2, <https://doi.org/10.1016/j.jtbi.2013.05.029> (PMC3753514).
