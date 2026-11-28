# Convergence of the response-time iteration

In the setting of [response-time analysis for fixed-priority periodic tasks](response-time-analysis-for-fixed-priority-periodic-tasks.md), with $W_i(r) = C_i + \sum_{j \in hp(i)} \lceil r/T_j \rceil C_j$ for $r \ge 0$, define $r^0 = 0$ and $r^{k+1} = W_i(r^k)$, so that $r^1 = C_i$. Then:

1. the sequence $(r^k)$ is nondecreasing, and every $r^k$ is at most every positive solution of $W_i(r) = r$;
2. if $r^{k+1} = r^k$ for some $k \ge 1$, then $r^k$ is the least positive solution of $W_i(r) = r$;
3. if $\sum_{j \in hp(i)} C_j/T_j < 1$, in particular if $\sum_{j \in hp(i) \cup \{i\}} C_j/T_j \le 1$, a positive solution exists and the sequence becomes constant after finitely many steps.

The iteration may be stopped as soon as some $r^k$ exceeds $T_i$: by 1, every positive solution is at least $r^k$, so there is no solution in $(0, T_i]$. The priority assignment is therefore infeasible for at least one choice of phases. A solution need not exist at all: with one higher-priority task with $C_j = T_j = 1$ and $C_i = 1$, $W_i(r) = 1 + \lceil r \rceil > r$ for every $r$.

**Proof.** $W_i$ is nondecreasing, so $r^0 \le r^1$ propagates to $r^k \le r^{k+1}$, and $r^k \le r^*$ for a fixed point $r^* > 0$ propagates in the same way. If $U = \sum_{j \in hp(i)} C_j/T_j < 1$, then $W_i(r) \le C_i + \sum_{j \in hp(i)} C_j + U r \le r$ for $r \ge R_0 = (C_i + \sum_{j \in hp(i)} C_j)/(1 - U)$, so the iterates stay in $[0, R_0]$, where $W_i$ takes only finitely many values; a nondecreasing sequence with finitely many values is eventually constant.

## Depends on

- [Response-time analysis for fixed-priority periodic tasks](response-time-analysis-for-fixed-priority-periodic-tasks.md)

## Sources

- N. Audsley, A. Burns, M. Richardson, K. Tindell and A. J. Wellings, "Applying new scheduling theory to static priority pre-emptive scheduling", *Software Engineering Journal* 8(5), 1993; author version <https://www.math.unipd.it/~tullio/RTS/2009/ABRTW-1993.pdf>, Section 3, equation (3): the iteration from $r_i^0 = 0$, its monotonicity, early termination once an iterate exceeds the deadline, and convergence when the processor utilisation is at most 100%.
