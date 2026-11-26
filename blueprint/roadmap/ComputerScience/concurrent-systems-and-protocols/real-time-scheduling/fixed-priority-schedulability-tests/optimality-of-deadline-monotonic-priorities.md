# Optimality of deadline-monotonic priorities

For a set of independent [constrained-deadline sporadic tasks](constrained-deadline-sporadic-tasks.md) on one processor, or of synchronous periodic tasks with constrained deadlines (all first released at time $0$), scheduled preemptively with fixed task priorities: if some priority assignment makes the task set schedulable, then the deadline-monotonic assignment, which orders priorities by nondecreasing relative deadline with ties broken arbitrarily, makes it schedulable. For implicit deadlines this is the [optimality of rate-monotonic priorities](../optimality-of-rate-monotonic-priorities.md). The statement fails for arbitrary deadlines ($D_i > T_i$ allowed) and for asynchronous periodic task sets.

## Depends on

- [Constrained-deadline sporadic tasks](constrained-deadline-sporadic-tasks.md)

## Expansion

This page becomes ready once these prerequisites are stated and its source is checked:

- the critical instant for constrained-deadline sporadic tasks: the worst-case response time of $\tau_i$ occurs for a job released together with jobs of all higher-priority tasks, which then recur as fast as allowed with maximal execution times (statement prerequisite of the proof);
- the swap argument: exchanging the priorities of two adjacent tasks that violate the deadline-monotonic order keeps a schedulable set schedulable (proof step);
- a check of J. Y.-T. Leung and J. Whitehead, "On the complexity of fixed-priority scheduling of periodic, real-time tasks", *Performance Evaluation* 2(4):237–250, 1982, the original source of the result.

## Sources

- R. I. Davis and A. Burns, "A survey of hard real-time scheduling for multiprocessor systems", *ACM Computing Surveys* 43(4), article 35, 2011; author version <https://www-users.york.ac.uk/~rd17/papers/MPSurveyv4.9.pdf>, Section 5: deadline monotonic priority assignment is optimal for synchronous periodic or sporadic task sets with constrained deadlines (attributed there to Leung and Whitehead, 1982), and is not optimal for arbitrary deadlines or asynchronous periodic task sets.
