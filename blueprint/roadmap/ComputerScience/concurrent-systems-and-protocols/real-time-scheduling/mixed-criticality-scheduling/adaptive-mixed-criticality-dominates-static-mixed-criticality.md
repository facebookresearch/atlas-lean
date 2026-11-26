# Adaptive mixed criticality dominates static mixed criticality

Under static mixed criticality, the response time of $\tau_i$ in a [dual-criticality sporadic task system](dual-criticality-sporadic-task-systems.md) is bounded by the least solution of

$$
R_i = C_i + \sum_{j \in hp(i)} \left\lceil \frac{R_i}{T_j} \right\rceil C_j(\min(L_i, L_j)) .
$$

Every sporadic task system that is schedulable under the rules and priority assignment of SMC with this test is also schedulable under the rules and priority ordering of AMC with the [AMC response-time bound](response-time-bound-for-adaptive-mixed-criticality.md), and some systems are schedulable under AMC but not SMC. The AMC equation is the SMC equation with part of the LO-criticality interference removed.

## Depends on

- [Dual-criticality sporadic task systems](dual-criticality-sporadic-task-systems.md)
- [Response-time bound for adaptive mixed criticality](response-time-bound-for-adaptive-mixed-criticality.md)

## Sources

- S. K. Baruah, A. Burns and R. I. Davis, "Response-time analysis for mixed criticality systems", *Proceedings of the 32nd IEEE Real-Time Systems Symposium*, 2011; author version <https://www-users.cs.york.ac.uk/robdavis/papers/MC_RTSS2011.pdf>, Section III.A (equation (2)) and Section IV.E, Theorem 2 with its proof and the example that follows.
