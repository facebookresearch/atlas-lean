# Mass conservation in a finite aggregation-breakage model

Take bins $i = 1, \dots, M$ ($M \ge 2$) for particles of mass $i$ with nonnegative populations $n_i(t)$, a symmetric aggregation
kernel $K_{ij} \ge 0$ with $K_{ij} = 0$ for $i + j > M$, and breakage rates $b_i \ge 0$ with $b_1 = 0$. For each bin with $b_i > 0$
let daughter coefficients $d_{ji} \ge 0$ be supported on $1 \le j < i$ with $\sum_j j\,d_{ji} = i$, so that $\sum_j d_{ji} > 1$;
bins with $b_i = 0$ carry no such identity. For a differentiable solution of

$$n_k' = \tfrac12 \sum_{i + j = k} K_{ij} n_i n_j - n_k \sum_j K_{kj} n_j + \sum_{i > k} d_{ki} b_i n_i - b_k n_k,$$

the total mass $\sum_k k\,n_k$ is constant; with breakage switched off ($b = 0$) the particle number $\sum_k n_k$ does not increase,
and with aggregation switched off ($K = 0$) it does not decrease. No continuum limit is claimed.

## Depends on

## Proof depends on

## Sources

- S. Kumar and D. Ramkrishna, On the solution of population balance equations by discretization—I. A fixed pivot technique, *Chemical Engineering Science* 51 (1996) 1311–1332, Sections 3.2–3.4.
