# Whole-network species balance

Consider a flowsheet with finitely many units in which each unit's holdup of species $s$ satisfies the unit balance: its derivative is the internal inflow from all units minus the internal outflow to all units, plus external inflow minus external outflow plus generation. Then for each species $s$ and time $t$, the derivative of the total holdup $\sum_u n_{s,u}(t)$ is $\sum_u \big(F^{in}_{s,u}(t) - F^{out}_{s,u}(t) + G_{s,u}(t)\big)$: every internal transfer cancels.
