# A potential that decreases along CDCL steps

Consider CDCL without restarts or clause deletion on a formula $F$, with states $(t, \mathcal L)$ of a trail $t$ and a set $\mathcal L$ of learned clauses; a step either decides a literal whose variable is not on the trail, or learns a new clause implied by $F$ and backjumps to a suffix of the trail. Fix finite sets $\mathcal V$ of variables and $\mathcal C$ of clauses. For a step $(t_1, \mathcal L_1) \to (t_2, \mathcal L_2)$ where the trail variables of both states lie in $\mathcal V$, the trail $t_1$ has distinct variables, and the learned clauses of both states lie in $\mathcal C$, the potential

$$\big(|\mathcal C| - |\mathcal L|\big)\big(|\mathcal V| + 1\big) + \big(|\mathcal V| - |t|\big)$$

(truncated subtraction on natural numbers) is strictly smaller at $(t_2, \mathcal L_2)$ than at $(t_1, \mathcal L_1)$.
