# Bang-bang sequential activation of unbranched metabolic pathways

**Setting.** An unbranched pathway converts a substrate through intermediates $x_1, \dots, x_n$ via reactions $0, 1, \dots, n$ with enzyme concentrations $u_0, \dots, u_n$:

$$
\dot x_i = v_{i-1} - v_i, \qquad i = 1, \dots, n, \qquad x(0) = 0 .
$$

Each rate is linear in its enzyme, $v_i = w_i(x_i)\,u_i$, with $w_i(0) = 0$ and $w_i' > 0$ (mass action, Michaelis–Menten and Hill kinetics qualify). Enzymes are limited: $u(t) \in \mathcal{U} = \{u \ge 0 : \sum_{i=0}^{n} u_i \le E_T\}$. The pathway must reach a prescribed steady-state flux $V$ at a free final time $t_f$, i.e. $x(t_f^-)$ must lie in $\mathcal{S} = \{x : \sum_i V/w_i(x_i) \le E_T\}$, while minimizing time plus weighted enzyme usage,

$$
\mathcal{J} = \int_0^{t_f} \bigl(1 + \alpha^\top u(t)\bigr)\,dt, \qquad \alpha \ge 0 .
$$

**Theorem.** The optimal control is unique and bang-bang with sequential activation: there are switching times $0 < t_0 < t_1 < \dots < t_{n-1} = t_f$ such that

$$
u_i^*(t) = \begin{cases} E_T, & t \in T_i, \\ 0, & t \notin T_i, \end{cases} \qquad T_0 = [0, t_0), \quad T_i = [t_{i-1}, t_i), \quad i = 1, \dots, n-1,
$$

and the intervals $T_0, \dots, T_{n-1}$ partition $[0, t_f)$. At each moment the entire enzyme budget is allocated to a single reaction, and the reactions are switched on one after another in pathway order; after $t_f$ the enzyme levels are set to the constants $u_i = V/w_i(x_i(t_f^-))$ that sustain the flux $V$.

## Proof sketch

The Hamiltonian is linear in $u$, $H = 1 + \alpha^\top u + \sum_i \lambda_i (v_{i-1} - v_i)$ with $v_i = w_i(x_i)u_i$, so Pontryagin's principle selects a vertex of the simplex $\mathcal{U}$ at almost every time: all enzyme goes to the reaction with the most negative switching function. Geometric arguments on the costates then show that the switching functions cross in pathway order, because reaction $i$ cannot run before its substrate $x_i$ has been built up ($w_i(0) = 0$).

## Related topics

- [Michaelis–Menten kinetics and the quasi-steady state](../../michaelis-menten-kinetics-and-the-quasi-steady-s/README.md)

## Sources

- Diego Oyarzún, Brian Ingalls, Richard Middleton and Dimitrios Kalamatianos, "Optimal Metabolic Pathway Activation", *IFAC Proceedings Volumes* 41 (2008), 12587–12592, <https://doi.org/10.3182/20080706-5-kr-1001.02130>. Preprint version: arXiv:0801.2447 (2008), Assumption 1, Problem 1, Theorem 1, <https://doi.org/10.48550/arXiv.0801.2447>.
