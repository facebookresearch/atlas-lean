# Variational inequality for Wardrop equilibria

If $f$ is a Wardrop equilibrium and $g$ is any flow feasible for the same demand $r$, then

$$C(f) \le \sum_{e \in E} \ell_e(f_e)\, g_e .$$

Equivalently $\sum_e \ell_e(f_e)(g_e - f_e) \ge 0$: with the latencies frozen at their
equilibrium values, no feasible flow is cheaper than $f$.

## Informally uses

- [Wardrop flows against a scaled demand](smul-sum-path-latency-mul-le.md): the case $c = 1$.

## Sources

- T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002), 236–259, §4 (inequality used in the proof of Theorem 4.5).
