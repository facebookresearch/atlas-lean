# Response-time bound for adaptive mixed criticality

For a [dual-criticality sporadic task system](dual-criticality-sporadic-task-systems.md) with positive execution budgets, $C_i(\mathrm{LO}) > 0$ for every task, under adaptive mixed criticality with a fixed priority order, let $hp(i)$ be the tasks of higher priority than $\tau_i$, and $hpH(i)$ and $hpL(i)$ the HI- and LO-criticality tasks of higher priority than $\tau_i$. Let $R_i^{\mathrm{LO}}$ be the least solution, when one exists, of

$$
R_i^{\mathrm{LO}} = C_i(\mathrm{LO}) + \sum_{j \in hp(i)} \left\lceil \frac{R_i^{\mathrm{LO}}}{T_j} \right\rceil C_j(\mathrm{LO})
$$

and, for $L_i = \mathrm{HI}$, $R_i^*$ the least solution, when one exists, of

$$
R_i^* = C_i(\mathrm{HI}) + \sum_{j \in hpH(i)} \left\lceil \frac{R_i^*}{T_j} \right\rceil C_j(\mathrm{HI}) + \sum_{k \in hpL(i)} \left\lceil \frac{R_i^{\mathrm{LO}}}{T_k} \right\rceil C_k(\mathrm{LO}) .
$$

If these solutions exist, $R_i^{\mathrm{LO}} \le D_i$ for every task and $R_i^* \le D_i$ for every HI-criticality task, the system is correct: in the LO mode every job meets its deadline, and in every behaviour, including those with a mode switch, every HI-criticality job does. LO-criticality tasks can delay a HI-criticality job only before $R_i^{\mathrm{LO}}$, since a job still running later has triggered the switch. Positive budgets are needed for the cap on LO interference: with period $10$ for both tasks, a higher-priority LO task with budget $2$ and deadline $2$ and a lower-priority HI task with $C(\mathrm{LO}) = 0$, $C(\mathrm{HI}) = 1$ and deadline $1$ pass the test ($R^{\mathrm{LO}} = 0$ and $R^* = 1$ for the HI task), but if both are released at $0$ the LO job runs first and the HI job cannot finish before $3$. The test is sufficient, not exact: exact analysis would have to examine every release pattern around the switch.

## Depends on

- [Dual-criticality sporadic task systems](dual-criticality-sporadic-task-systems.md)

## Proof depends on

- [Response-time analysis for fixed-priority periodic tasks](../fixed-priority-schedulability-tests/response-time-analysis-for-fixed-priority-periodic-tasks.md): the standard recurrence for the stable modes.

## Sources

- S. K. Baruah, A. Burns and R. I. Davis, "Response-time analysis for mixed criticality systems", *Proceedings of the 32nd IEEE Real-Time Systems Symposium*, 2011; author version <https://www-users.cs.york.ac.uk/robdavis/papers/MC_RTSS2011.pdf>, Section IV.A (equations (4) and (5) for the stable modes and the discussion of exact analysis) and Section IV.B (sufficient analysis, method 1, equations (6)–(7)), the test known as AMC-rtb. The source writes $C_i$ in equation (4) and defines $hpH(i)$, $hpL(i)$ with priority "higher than, or equal to" that of $\tau_i$; its worked values for Example 2 use $C_i(\mathrm{LO})$ in the LO mode and count $\tau_i$ once, which is the form stated here.
