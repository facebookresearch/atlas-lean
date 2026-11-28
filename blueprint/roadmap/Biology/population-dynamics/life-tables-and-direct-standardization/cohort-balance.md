# Cohort size is initial size minus cumulative deaths plus net migration

Let $(P_t)$, $(D_t)$ and $(M_t)$ be real sequences indexed by the times $t \in \mathbb{N}$ with
$P_{t+1} = P_t - D_t + M_t$ for every $t$. Then, for every $T \in \mathbb{N}$,
$P_T = P_0 - \sum_{t < T} D_t + \sum_{t < T} M_t$, the sums running over $t = 0, \dots, T - 1$; for
$T = 0$ both sums are empty, hence $0$. In the demographic reading, $P_t$ is the size of a cohort or
population at time $t$, and $D_t$ and $M_t$ are its deaths and its net migration, together with any
error term, between times $t$ and $t + 1$. No sign condition is needed.

Source: Methods Protocol for the Human Mortality Database, version 6, eqs. (10)–(11).
