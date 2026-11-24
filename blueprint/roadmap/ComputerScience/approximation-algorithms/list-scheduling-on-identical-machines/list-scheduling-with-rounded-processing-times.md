# List scheduling with rounded processing times

Let a finite list of jobs have real processing times $p_j\ge0$, and let $\delta>0$. On $m\ge1$ identical machines without
precedence constraints, run list scheduling on the natural tick counts $\tilde p_j=\lceil p_j/\delta\rceil$ in any order,
with natural-number makespan $\tilde C_{\mathrm{list}}$. For every assignment $S=(S_1,\dots,S_m)$ of each job occurrence
exactly once, put $C(S)=\max_i\sum_{j\in S_i}p_j$. Cast the tick makespan to the reals. Then

$$\delta\,\tilde C_{\mathrm{list}} \le \Bigl(2 - \frac1m\Bigr)\Bigl(C(S) + \delta \max_i \lvert S_i\rvert\Bigr),$$

by Graham's bound applied to the tick counts and the rounding bound for $S$. No claim is made that the list schedule is optimal
or that its makespan decreases as $\delta$ decreases.

## Depends on

## Proof depends on

- [Graham's bound for list scheduling](list-schedule-approx.md)
- [Rounding processing times to ticks](rounding-processing-times-to-ticks.md)

## Sources

- R. L. Graham, "Bounds for certain multiprocessing anomalies", *Bell System Technical Journal* 45(9) (1966), 1563–1581.
