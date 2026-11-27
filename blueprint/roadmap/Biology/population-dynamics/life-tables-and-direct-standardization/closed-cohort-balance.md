# Closed cohort size is initial size minus cumulative deaths

Let $(P_t)$ and $(D_t)$ be real sequences indexed by the times $t \in \mathbb{N}$ with
$P_{t+1} = P_t - D_t$ for every $t$: a closed cohort, with no migration and no error term, whose
size changes only by the deaths $D_t$ between times $t$ and $t + 1$. Then
$P_T = P_0 - \sum_{t < T} D_t$ for every $T \in \mathbb{N}$, the sum running over
$t = 0, \dots, T - 1$ and being empty, hence $0$, for $T = 0$. No sign condition is needed. This is
the [open cohort balance](cohort-balance.md) with zero net migration.
