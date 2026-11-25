# Junction supply feasibility

For a network with finitely many links and commodities, link tails and heads, and per-link free-flow speed $v_f$, wave speed $w$, jam density $k_j$ and first-cell density $k_1$, turning flows $q_c(e, e')$ are supply feasible when for every link $e'$,

$$\sum_c \sum_{e : \mathrm{head}(e) = \mathrm{tail}(e')} q_c(e, e') \le \min\{w_{e'}(k_{j,e'} - k_{1,e'}),\ q_{max,e'}\},$$

with $q_{max} = v_f w k_j/(v_f + w)$ the link capacity, which is $0$ when $v_f + w = 0$, by the convention $x/0 = 0$.
