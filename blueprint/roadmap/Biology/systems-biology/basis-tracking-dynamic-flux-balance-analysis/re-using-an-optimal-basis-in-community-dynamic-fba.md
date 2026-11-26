# Re-using an optimal basis in community dynamic FBA

**Community dynamic FBA.** Organisms $i = 1, \dots, p$ with biomass $x_i$ share nutrients $y$. At each time, organism $i$ chooses internal fluxes $\phi_i \in \mathbb{R}^{d}$ solving a linear program

$$\max\ \gamma_i \cdot \phi_i \quad \text{s.t.}\quad A_i \phi_i \le c_i(t),\ \ \Gamma_i^\dagger \phi_i = 0,$$

where $\gamma_i$ is the biomass objective, $\Gamma_i^\dagger$ the internal stoichiometry (steady state), and the bounds $c_i(t)$ depend on the current nutrient concentrations (uptake limits). Then

$$\frac{dx_i}{dt} = x_i\, \gamma_i \cdot \phi_i(t), \qquad \frac{dy}{dt} = -\sum_i x_i\, \Gamma_i^\ast \phi_i(t),$$

with $\Gamma_i^\ast$ the exchange stoichiometry.

**Basic solutions.** Write the program in standard form $\max\, \tilde\gamma \cdot w$, $[\tilde A\ \ I]\, w = c$, $w \ge 0$ (free fluxes split into positive and negative parts, $s$ the slacks). For an index set $J = \{k_1, \dots, k_n\}$ with $B_J$ (the corresponding columns of $[\tilde A\ \ I]$) invertible, let $w_J(c)$ have entries $(B_J^{-1} c)_j$ at position $k_j$ and $0$ off $J$. A bounded feasible program has a basic optimal solution $w = w_J(c)$; it is degenerate if it has a basic variable equal to zero, in which case several index sets give the same $w$.

**Forward simulation without re-solving.** Fix an optimal basis $J$ at time $t_0$. As long as $w_J(c(t)) \ge 0$, the vector $w_J(c(t))$ is still optimal (the reduced costs do not depend on $c$), so the fluxes $\phi_i(t)$ are an explicit linear function of $c_i(t)$ and the ODEs above can be integrated with no further optimization. The linear program must be re-solved only when some basic variable reaches $0$.

**Choosing among degenerate bases (Lemma).** For a basic optimal solution $w$, there exists a basic index set $J$ such that the velocity $\dot w = w_J(\dot c)$ satisfies $[\tilde A\ \ I]\, \dot w = \dot c$ and $\dot w_j \ge 0$ whenever $(w_J)_j = 0$, and $\dot w$ is optimal among all basic index sets of $w$. Such a $J$ is found by solving the auxiliary linear program

$$\max\ \gamma_i \cdot \dot\phi_i \quad \text{s.t.} \quad a_j \cdot \dot\phi_i \le \frac{d c_{ij}}{dt} \ \text{ for all constraints } a_j \text{ active at } \phi_i,$$

and keeping the $d$ active constraints whose slacks are non-basic in its solution.

## Expansion

Optimality of a basis is certified by the sign of the reduced costs $\tilde\gamma_N - \tilde\gamma_J B_J^{-1} N$, which involve only the constraint matrix and objective, not $c$; feasibility $B_J^{-1} c \ge 0$ is the only condition that changes with time, so the basis stays optimal until a basic variable crosses zero. The choice among degenerate bases matters: for $\max (v_1 + v_2)$ with $v_1 \le 10$, $v_2 \le 10$, $v_1 + 2v_2 \le 30 - t$, the solution at $t = 0$ is $w = (10, 10, 0, 0, 0)$ with three possible bases, yielding $(10 - t, 10, t, 0, 0)$ (feasible but not optimal), $(10, 10 - t/2, 0, t/2, 0)$ (optimal until $t = 20$) and $(10, 10, 0, 0, -t)$ (infeasible); only the second is the right one for this $c(t)$, and a different bound trajectory selects a different basis. The auxiliary program on the active constraints picks the basis whose motion stays feasible and optimal for the given $\dot c$. On a four-species community this reduces the number of linear programs solved by at least $91\%$ relative to re-optimizing at each step.

## Sources

- J. D. Brunner, N. Chia, "Minimizing the number of optimizations for efficient community dynamic flux balance analysis", PLoS Computational Biology 16 (2020) e1007786, Methods (Equations (10)–(19), Definition 1, Lemma 1, Example 1, Algorithm 1), <https://doi.org/10.1371/journal.pcbi.1007786> (PMC7546477).
