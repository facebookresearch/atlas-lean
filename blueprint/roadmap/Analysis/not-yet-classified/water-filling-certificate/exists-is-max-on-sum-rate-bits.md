# Water-filling solves the parallel Gaussian power allocation problem

Let $\iota$ be a finite set of modes with gains $\lambda_i \ge 0$, and let $P \ge 0$. The sum rate in bits of a power allocation $p$ is $R(p) = \sum_i \frac{\log(1 + \lambda_i p_i)}{2 \log 2}$, and the admissible allocations are those with $p_i \ge 0$ for all $i$ and $\sum_i p_i \le P$. For a level $\nu$, the water-filling allocation is $w_i(\nu) = \max(\nu - 1/\lambda_i, 0)$ if $\lambda_i > 0$ and $w_i(\nu) = 0$ otherwise.

There is an admissible allocation $p$ that maximizes $R$ over all admissible allocations and satisfies:

1. $p_i = 0$ whenever $\lambda_i = 0$;
2. if $P > 0$ and $\lambda_i > 0$ for some $i$, then there is $\nu > 0$ with $\sum_{i : \lambda_i > 0} \max(\nu - 1/\lambda_i, 0) = P$ and $p = w(\nu)$, and for every $i$, $\frac{\lambda_i}{1 + \lambda_i p_i} \le \nu^{-1}$, with equality when $p_i > 0$;
3. if $P = 0$ or $\lambda_i = 0$ for all $i$, then $p = 0$.
