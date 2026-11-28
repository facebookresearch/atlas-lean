# Throughput bound for a two-station serial line

Consider two single-server stations in series, numbered $0$ (upstream) and $1$ (downstream). Fix $t>0$ and take the initial
state just after all events at time $0$. Write $W_i$ for the number of jobs initially at station $i$, including any job in
service. For each station, list the $D_i$ jobs whose service finishes in $(0,t]$ in completion order. Record the full
nonpreemptive service interval $[a_{ij},b_{ij}]$ of job $j$, including any part before time $0$. Thus $0<b_{ij}\le t$,
$b_{ij}-a_{ij}\ge 1/\mu_i$ for a rate $\mu_i>0$, and $b_{ij}\le a_{ik}$ for $j<k$. An upstream job whose service starts at
or before zero must be one of the initial upstream jobs.

Assign each downstream completion to a distinct source: an initial downstream job, or an upstream job that finishes in
$(0,t]$ no later than the start of its downstream service. The same upstream job cannot supply two downstream completions.
In particular, a downstream job that starts at or before zero must be initial. Upstream completions at time zero are
outside the window; a job transferred at that time belongs to the initial downstream stock.

The in-window service on jobs that complete is

$$B_i=\sum_{j=1}^{D_i}\bigl(b_{ij}-\max(0,a_{ij})\bigr).$$

The credit for service before zero is

$$\beta_i=\sum_{j=1}^{D_i}\frac{\max(0,-a_{ij})}{b_{ij}-a_{ij}}.$$

At most the first interval can cross zero, so $\beta_i$ is the fraction of that job already served at zero, or zero if
no completed job crosses zero. Both sums are zero for an empty list. The conclusion is

$$D_i\le \beta_i+\mu_i B_i\quad(i=0,1),\qquad
\frac{D_1}{t}\le\min(\mu_0,\mu_1)+\frac{W_0+W_1}{t}.$$

To see the station bound, split each job's unit completion count into its before-window and in-window fractions of the
full service duration. The first fraction contributes to $\beta_i$. Since the full duration is at least $1/\mu_i$, the
second fraction is at most $\mu_i$ times that job's in-window service. Within each station the clipped intervals are
nonoverlapping, so their total length $B_i$ is at most $t$. Also $\beta_i\le W_i$: any nonzero credit is at most one and
comes from an initially present job. Therefore $D_i\le W_i+\mu_i t$. Counting the distinct sources gives
$D_1\le W_1+D_0$. Combining this with the upstream station bound and comparing with the downstream station bound gives
the throughput inequality.

The in-window service on jobs that complete is no greater than the station's total in-window busy time, which may also
include service on a job still unfinished at time $t$. Thus the station inequality with $B_i$ is at least as strong as
one using total busy time. The bound is deterministic and finite-window. Nominal rates alone do not imply it:
exponential service times can be arbitrarily short with positive probability.

## Sources

- W. J. Hopp and M. L. Spearman, *Factory Physics*, 3rd edition, Waveland Press, 2011, Chapter 7: the bottleneck-rate concept that motivates this bound. The finite-history bound and its proof are derived on this page.
