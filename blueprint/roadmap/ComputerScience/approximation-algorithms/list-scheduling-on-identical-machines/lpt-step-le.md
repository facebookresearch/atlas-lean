# The LPT placement step

Let $m \ge 1$ and let a list of job processing times, in
nonincreasing order, be the concatenation of a list $P$, a job $p$ and a list $R$. Let $\sigma$
be a schedule of the jobs $P$ on $m$ machines, with load $\ell_i$ on machine $i$, and let
$L = \min_i \ell_i$ be the load of a least-loaded machine. Then for every schedule $\tau$ of all
the jobs on the $m$ machines, with makespan $M$, we have $3m(L + p) \le (4m - 1)M$.
