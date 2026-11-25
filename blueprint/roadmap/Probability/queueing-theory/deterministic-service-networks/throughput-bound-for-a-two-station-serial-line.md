# Throughput bound for a two-station serial line

Consider two single-server stations in series, each serving one job at a time without preemption, where every job needs a
service time of at least $1/\mu_i$ at station $i$, $\mu_i > 0$, and jobs are neither duplicated nor lost. Let $W_i(0)$ count the
jobs at station $i$ at time $0$, including one in service, and let $\beta_i \in [0, 1]$ with $\beta_i \le W_i(0)$ be the service
already completed on the initially in-service job, expressed as a fraction of that job's total service requirement: if its
elapsed and total service times are $a_i$ and $s_i$, use $\beta_i=a_i/s_i$; if no job is initially in service, use $\beta_i=0$.
The initial state is taken after all events at time $0$. All new arrivals enter station $1$, and a job moves from station $1$
to station $2$ exactly once. Let $D_i(t)$ count completions in $(0,t]$, so $D_i(0)=0$, and let $\mathrm{busy}_i(t)$ count only
service time in that window. At simultaneous events use the same right-closed window convention at both stations.

If the initial job completes during the window, its remaining service is $(1-\beta_i)s_i\ge(1-\beta_i)/\mu_i$; every later
completed job consumes at least $1/\mu_i$ service time in the window. If an initially in-service job does not complete, the
station, which does not preempt, has no completions. If no job is initially in service, $\beta_i=0$ and every completed job,
including one started later from the queue or by an arrival, consumes its whole service requirement, at least $1/\mu_i$,
inside the window.
Thus $D_i(t) \le \beta_i + \mu_i\,\mathrm{busy}_i(t)$, with $\mathrm{busy}_i(t)\le t$, and
$D_2(t) \le W_2(0) + D_1(t)$,
so for $t > 0$

$$\frac{D_2(t)}{t} \le \min(\mu_1, \mu_2) + \frac{W_1(0) + W_2(0)}{t} .$$

This is a deterministic bound on one finite history. Nominal rates alone do not give it: exponential service times can be
arbitrarily short with positive probability. Stationary stochastic models of lines are outside this result.

## Depends on

## Proof depends on

## Sources

- W. J. Hopp and M. L. Spearman, *Factory Physics*, 3rd edition, Waveland Press, 2011, Chapter 7: the bottleneck-rate concept that motivates this bound. The finite-history bound and its proof are derived on this page.
