# Deadline-monotonic order within each criticality level is optimal

For a [dual-criticality sporadic task system](dual-criticality-sporadic-task-systems.md) with constrained deadlines, under static mixed criticality with its response-time test (the test stated on [the dominance page](adaptive-mixed-criticality-dominates-static-mixed-criticality.md)) or under adaptive mixed criticality with the [AMC-rtb test](response-time-bound-for-adaptive-mixed-criticality.md), with positive execution budgets, if some priority ordering makes the system schedulable then one does in which tasks of the same criticality level are in deadline-monotonic order. Hence Audsley's algorithm, which assigns the lowest priority to some task that is schedulable there and recurses, needs to try only two candidates at each level: the LO- and the HI-criticality task with the largest deadline, for at most $2n - 1$ tests instead of $n(n + 1)/2$.

**Proof idea.** If $\tau_i$ is schedulable at the lowest priority and $\tau_k$ has the same criticality and a larger deadline, then $\tau_k$ placed there suffers exactly the same interference: the busy period of the lowest priority level contains a single execution of $\tau_i$ and a single execution of $\tau_k$ in both orders, since all deadlines are at most the periods and $R_i > 0$, so $R_k = R_i \le D_i \le D_k$. Positive budgets are needed for this count: with period $10$, $(C_i, D_i) = (0, 1)$ and $(C_k, D_k) = (2, 3)$, the least solution for $\tau_i$ at the lowest level is $0$, and the busy period contains no execution of $\tau_k$, while $R_k = 2$. A task needing no work meets its deadlines at any priority.

## Depends on

- [Dual-criticality sporadic task systems](dual-criticality-sporadic-task-systems.md)
- [Response-time bound for adaptive mixed criticality](response-time-bound-for-adaptive-mixed-criticality.md)
- [Adaptive mixed criticality dominates static mixed criticality](adaptive-mixed-criticality-dominates-static-mixed-criticality.md)

## Sources

- S. K. Baruah, A. Burns and R. I. Davis, "Response-time analysis for mixed criticality systems", *Proceedings of the 32nd IEEE Real-Time Systems Symposium*, 2011; author version <https://www-users.cs.york.ac.uk/robdavis/papers/MC_RTSS2011.pdf>, Section III.B (priority assignment for SMC by Audsley's algorithm and Theorem 1 with its proof) and Section IV.D (the same property for AMC).
