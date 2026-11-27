# Resilient consensus protocols

Fix assumptions $A$ on processor and communication synchrony, a fault type $F$, a number $N$ of processors with initial values in a set $V$, and an integer $t$ with $0 \le t \le N$. A protocol is a *$t$-resilient consensus protocol* if, for every set $C$ of at least $N - t$ processors and every run satisfying $A$ in which the processors in $C$ are correct and the behavior of the others is allowed by $F$, the following hold.

- *Consistency* (agreement): no two processors in $C$ decide differently.
- *Termination:* if the run is infinite, every processor in $C$ decides.
- *Strong unanimity:* if all initial values are $v$ and a processor in $C$ decides, it decides $v$.

*Weak unanimity* replaces strong unanimity by: if all initial values are $v$, $C$ contains all processors, and some processor decides, then it decides $v$.

## Depends on

- [Timed message-passing runs](../distributed-execution-models/timed-message-passing-runs.md)
- [Fail-stop, omission and Byzantine faults](../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- C. Dwork, N. Lynch and L. Stockmeyer, "Consensus in the presence of partial synchrony", *Journal of the ACM* 35(2):288–323, 1988, Section 2.4
