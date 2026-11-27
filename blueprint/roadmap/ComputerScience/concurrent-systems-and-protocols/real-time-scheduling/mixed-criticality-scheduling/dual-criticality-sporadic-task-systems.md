# Dual-criticality sporadic task systems

A *dual-criticality* sporadic task $\tau_i = (T_i, D_i, C_i(\mathrm{LO}), C_i(\mathrm{HI}), L_i)$ is a [constrained-deadline sporadic task](../fixed-priority-schedulability-tests/constrained-deadline-sporadic-tasks.md) with minimum inter-arrival time $T_i$ and relative deadline $D_i \le T_i$, a criticality level $L_i \in \{\mathrm{LO}, \mathrm{HI}\}$ with $\mathrm{HI} > \mathrm{LO}$, and execution-time bounds $C_i(\mathrm{LO}) \le C_i(\mathrm{HI})$ certified at the two levels of assurance; $C_i = C_i(L_i)$. In a run, the *criticality level of the behaviour* is the least level $L$ such that no job executes for more than its $C(L)$; behaviours in which some job executes for more than its $C(\mathrm{HI})$ have no level and are not considered. Correctness: for each level $L$, in every behaviour of level $L$, every job of every task of criticality at least $L$ meets its deadline. Tasks are scheduled by a preemptive fixed-priority dispatcher on one processor, with execution times monitored:

1. *static mixed criticality* (SMC): no job executes for more than its $C_i$;
2. *adaptive mixed criticality* (AMC): the system starts in mode LO; if any job executes for $C(\mathrm{LO})$ without completing, the mode switches to HI, and from then on no LO-criticality job executes.

## Depends on

- [Constrained-deadline sporadic tasks](../fixed-priority-schedulability-tests/constrained-deadline-sporadic-tasks.md)

## Sources

- S. K. Baruah, A. Burns and R. I. Davis, "Response-time analysis for mixed criticality systems", *Proceedings of the 32nd IEEE Real-Time Systems Symposium*, 2011; author version <https://www-users.cs.york.ac.uk/robdavis/papers/MC_RTSS2011.pdf>, Section II (system model, Definition 1 and the correctness criterion, restricted there to two levels and constrained deadlines), Section III (SMC) and Section IV (the AMC run-time rules).
- S. Vestal, "Preemptive scheduling of multi-criticality systems with varying degrees of execution time assurance", *Proceedings of the 28th IEEE Real-Time Systems Symposium*, 2007, which introduced the model with several execution-time estimates per task.
