# Throughput bound for a two-station serial line

Consider two single-server stations in series, each serving one job at a time without preemption, where every job needs a
service time of at least $1/\mu_i$ at station $i$, $\mu_i > 0$, and jobs are neither duplicated nor lost. Let $W_i(0)$ count the
jobs at station $i$ at time $0$, including one in service, and let $\beta_i \in [0, 1]$ with $\beta_i \le W_i(0)$ be the service
already completed on the initially in-service job, expressed as a fraction of that job's total service requirement: if its
elapsed and total service times are $a_i$ and $s_i$, use $\beta_i=a_i/s_i$; if no job is initially in service, use $\beta_i=0$.
The initial state is taken after all events at time $0$. All new arrivals enter station $1$, and a job moves from station $1$
to station $2$ exactly once. Let $D_i(t)$ count completions in $(0,t]$, so $D_i(0)=0$, and let $\mathrm{busy}_i(t)$ count only
service time in that window. At simultaneous events use the same right-closed window convention at both stations.

For the finite-window formulation, list the full service requirements $s_{i,j}$ of the $D_i(t)$ completed jobs at station $i$ in completion order. Each satisfies $s_{i,j}\ge 1/\mu_i$. Use the weight $w_{i,1}=1-\beta_i$ for the first completion (if it exists) and $w_{i,j}=1$ for later completions. If no job is initially in service, $\beta_i=0$ and all weights are one. If the job initially in service does not complete, nonpreemption implies that the completion list is empty.

The finite history gives two accounting conditions. The service on completed jobs within the window is at most the busy time, so $\sum_{j=1}^{D_i(t)} w_{i,j}s_{i,j}\le \mathrm{busy}_i(t)\le t$. And every downstream completion comes from an initial job there or an upstream completion in the same window, so $D_2(t)\le W_2(0)+D_1(t)$. The Lean theorem takes these two conditions as hypotheses; it does not model the service or arrival events themselves.

Since the weights are nonnegative and their sum is at least $D_i(t)-\beta_i$, the service lower bound gives $D_i(t)\le \beta_i+\mu_i\,\mathrm{busy}_i(t)$. Using the transfer condition, $\beta_i\le W_i(0)$, and the busy-time bound gives, for $t>0$,

$$\frac{D_2(t)}{t} \le \min(\mu_1, \mu_2) + \frac{W_1(0) + W_2(0)}{t} .$$

This is a deterministic bound on one finite history. Nominal rates alone do not give it: exponential service times can be
arbitrarily short with positive probability. Stationary stochastic models of lines are outside this result.

## Sources

- W. J. Hopp and M. L. Spearman, *Factory Physics*, 3rd edition, Waveland Press, 2011, Chapter 7: the bottleneck-rate concept that motivates this bound. The finite-history bound and its proof are derived on this page.
