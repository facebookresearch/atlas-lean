# Price of anarchy 4/3 for affine latencies

Suppose every latency is affine, $\ell_e(x) = a_e x + b_e$ with $a_e, b_e \ge 0$. If $f$ is a
Wardrop equilibrium and $g$ is any flow feasible for the same demand, then

$$C(f) \le \tfrac43\, C(g).$$

So the price of anarchy of selfish routing with affine latencies is at most $4/3$; Pigou's
network shows that $4/3$ is attained.

The proof combines the variational inequality $C(f) \le \sum_e \ell_e(f_e) g_e$ with the
pointwise bound $a_e f_e g_e \le a_e g_e^2 + a_e f_e^2 / 4$, which gives
$C(f) \le C(g) + C(f)/4$.

## Informally uses

- [Variational inequality for Wardrop equilibria](cost-le-sum-latency-mul-edge-flow.md): the
  first step.

## Background

- [Pigou's network attains the bound 4/3](pigou-cost-wardrop-eq.md): tightness.

## Sources

- T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002), 236–259, Theorem 4.5.
