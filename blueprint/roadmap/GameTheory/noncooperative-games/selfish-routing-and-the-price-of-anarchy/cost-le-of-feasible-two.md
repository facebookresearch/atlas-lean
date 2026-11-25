# Selfish routing costs at most an optimal routing of twice the traffic

Suppose every latency $\ell_e$ is nonnegative and nondecreasing on $[0, \infty)$. If $f$ is a
Wardrop equilibrium feasible for the demand $r$ and $g$ is any flow feasible for the demand $2r$,
then $C(f) \le C(g)$.

So the cost of selfish routing never exceeds the cost of routing twice as much traffic optimally,
however steep the latencies.

## Informally uses

- [Bicriteria bound for selfish routing](mul-cost-le-of-feasible-one-add.md): the case $\gamma = 1$.

## Sources

- T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002), 236–259, Theorem 3.1.
