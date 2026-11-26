# Deterministic equivalent of a two-stage stochastic linear program

Let $X$ be a nonempty polyhedron of first-stage decisions, scenarios $s = 1, \dots, m$ have probabilities $p_s \ge 0$ with $\sum_s p_s = 1$, and let $Q_s(x) = \inf\{q_s^{\mathsf T}y : W_sy = h_s - T_sx,\ y \ge 0\}$ be finite for every $x \in X$ (relatively complete and bounded recourse). Then $\inf_{x \in X}(c^{\mathsf T}x + \sum_s p_sQ_s(x))$ equals the infimum of the linear program in $(x, y_1, \dots, y_m)$ minimizing $c^{\mathsf T}x + \sum_s p_sq_s^{\mathsf T}y_s$ subject to $x \in X$, $W_sy_s = h_s - T_sx$, $y_s \ge 0$, with one shared $x$; optimal solutions correspond. Letting the first-stage decision depend on the scenario gives a relaxation, whose value can be strictly smaller.

## Sources

- A. Shapiro, D. Dentcheva and A. Ruszczyński, *Lectures on Stochastic Programming: Modeling and Theory*, SIAM, 2009, Section 1.2.1, two-stage inventory model: "In the special case of finitely many demand scenarios ... the two-stage problem (1.23)–(1.24)", <https://bpb-us-e1.wpmucdn.com/sites.gatech.edu/dist/4/1470/files/2021/03/SPbook.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
