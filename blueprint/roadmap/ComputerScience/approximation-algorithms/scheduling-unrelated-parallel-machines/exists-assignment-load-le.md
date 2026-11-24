# Lenstra–Shmoys–Tardos rounding theorem

Let $M$ be a finite set of machines and $J$ a finite set of jobs, let $p_{ij} \in \mathbb N$ be
the processing time of job $j$ on machine $i$, and let $d_i \in \mathbb N$ for each machine and
$t \in \mathbb N$. Suppose $x : M \times J \to \mathbb R$ satisfies

- $x_{ij} \ge 0$, and $x_{ij} = 0$ whenever $p_{ij} > t$;
- $\sum_{i} x_{ij} = 1$ for every job $j$;
- $\sum_{j} p_{ij}\, x_{ij} \le d_i$ for every machine $i$.

Then there is an assignment $\sigma : J \to M$ with $p_{\sigma(j) j} \le t$ for every job $j$ and

$$\sum_{j : \sigma(j) = i} p_{ij} \le d_i + t \quad\text{for every machine } i.$$

Lenstra, Shmoys and Tardos prove more: every vertex of this polytope can be rounded in polynomial
time, because its support is a pseudoforest. Taking $d_i = t = T$ and searching for the least $T$
for which the linear program is feasible gives a schedule of makespan at most twice the optimum,
the $2$-approximation of their Theorem 2.

## Background

- [List scheduling on identical machines](../list-scheduling-on-identical-machines/README.md):
  background, the identical-machines case.

## Sources

- J. K. Lenstra, D. B. Shmoys and É. Tardos, "Approximation algorithms for scheduling unrelated
  parallel machines", Math. Programming 46 (1990), 259–271, Theorem 1 (rounding theorem) and
  Theorem 2.
- D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge
  University Press, 2011, §11.1.
