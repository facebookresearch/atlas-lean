# Graham's bound for LPT scheduling

Let $m \ge 1$ and let $J$ be a list of natural numbers
(job processing times). Let $C$ be the makespan of the schedule of $J$ on $m$ machines produced
by the LPT algorithm, and let $M$ be the makespan of any schedule $\tau$ of $J$ on $m$ machines.
Then $3mC \le (4m - 1)M$, that is, $C \le (4/3 - 1/(3m))M$.

## Sources

- Graham, "Bounds on multiprocessing timing anomalies", SIAM J. Appl. Math. 17 (1969).
