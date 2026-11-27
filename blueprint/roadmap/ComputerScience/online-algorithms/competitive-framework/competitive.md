# Competitive

A strategy $A$ for an online problem is $(c, b)$-competitive when $c \ge 0$, $b \ge 0$, $A$ is feasible (every legal input produces a feasible trace), and for every legal input $\sigma$ its cost satisfies $\mathrm{ALG}(\sigma) \le c \cdot \mathrm{OPT}(\sigma) + b$, the optimum taken in $[0, \infty]$. The bound is stated with inequalities, never division, so when $\mathrm{OPT} = 0$ and $b = 0$ it says $\mathrm{ALG} = 0$. Feasibility is part of the definition: a strategy giving only forbidden answers at zero cost is not competitive.
