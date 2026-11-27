# Adaptive mixed criticality dominates static mixed criticality

The static mixed criticality (SMC) response-time test of a [dual-criticality sporadic task system](dual-criticality-sporadic-task-systems.md) checks, for every task $\tau_i$, that the equation

$$
R_i = C_i + \sum_{j \in hp(i)} \left\lceil \frac{R_i}{T_j} \right\rceil C_j(\min(L_i, L_j)) .
$$

has a solution and that its least solution satisfies $R_i \le D_i$; when every check passes, the system is correct under the rules of SMC: in each behaviour of level $L$, every job of a task of criticality at least $L$ meets its deadline. LO-criticality jobs may miss their deadlines in a behaviour of level HI: with period $10$ for both tasks, a higher-priority HI task with $C(\mathrm{LO}) = 1$, $C(\mathrm{HI}) = 3$ and deadline $3$ and a lower-priority LO task with $C = 1$ and deadline $2$ pass both checks ($R = 3$ and $R = 2$), but if both are released at $0$ and the HI job executes for $3$, the LO job finishes at $4$. This is a test, not a bound on the response time of a task that fails its check: with two tasks of one criticality, each needing one unit, the higher-priority one with period and deadline $2$ and the lower-priority one with period and deadline $1$, the least solution of $R = 1 + \lceil R/2 \rceil$ is $2$, while with synchronous releases the successive jobs of the lower task have responses $2, 3, 4, \dots$, since its earlier jobs carry in.

Every sporadic task system that is schedulable under the rules and priority assignment of SMC with this test is also schedulable under the rules and priority ordering of AMC with the [AMC response-time bound](response-time-bound-for-adaptive-mixed-criticality.md), and some systems are schedulable under AMC but not SMC. The AMC equation is the SMC equation with part of the LO-criticality interference removed.

## Depends on

- [Dual-criticality sporadic task systems](dual-criticality-sporadic-task-systems.md)
- [Response-time bound for adaptive mixed criticality](response-time-bound-for-adaptive-mixed-criticality.md)

## Sources

- S. K. Baruah, A. Burns and R. I. Davis, "Response-time analysis for mixed criticality systems", *Proceedings of the 32nd IEEE Real-Time Systems Symposium*, 2011; author version <https://www-users.cs.york.ac.uk/robdavis/papers/MC_RTSS2011.pdf>, Section III.A (equation (2)) and Section IV.E, Theorem 2 with its proof and the example that follows.
