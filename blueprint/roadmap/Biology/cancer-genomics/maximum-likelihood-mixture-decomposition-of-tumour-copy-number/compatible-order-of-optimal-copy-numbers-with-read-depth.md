# Compatible order of optimal copy numbers with read depth

Two vectors $a, b \in \mathbb{R}^m$ have **compatible order** if for all $1 \le i,j \le m$,

$$a_i \le a_j \iff b_i \le b_j .$$

(A constant vector has compatible order with every vector.)

In the multinomial read-depth model of a tumour mixture, let $\Omega_{m,n,k}$ be the set of pairs $(C,\mu)$ with $C \in \{0,\dots,k\}^{m\times n}$, first column $c_1 = (2,\dots,2)$ (normal genome), and $\mu \in \Delta_{n-1}$. Let

$$p^* = \widehat{C^*\mu^*} = \arg\min_{p \in \{\widehat{C\mu} : (C,\mu)\in\Omega_{m,n,k}\}} \Big(-\sum_i r_i \log p_i\Big)$$

for an observed read depth vector $r \in \mathbb{N}^m$. Then:

1. $p^*$ and $r$ have compatible order.
2. If $n = 2$ (one tumour clone plus normal admixture) and $\mu^*_2 > 0$, then $r$ and the tumour count vector $c^*_2$ have compatible order.

**Consequence.** For $n = 2$ one only needs to enumerate count vectors $c_2 \in \{0,\dots,k\}^m$ whose order agrees with that of $r$. There are $O(m^k)$ such vectors, and they can be enumerated in $O(m^{k+1})$ time, so the maximum likelihood mixture decomposition is solvable in time polynomial in $m$ for fixed $k$, each candidate requiring a one-dimensional convex optimisation over $\mu_2$.

## Expansion

If two intervals were out of order, say $r_i < r_j$ but $p^*_i > p^*_j$, swapping the two coordinates of $p^*$ strictly decreases $-\sum r_\ell \log p_\ell$ (a rearrangement inequality), and the swapped vector is still feasible because swapping the corresponding rows of $C$ keeps $(C,\mu)$ in $\Omega_{m,n,k}$. For $n = 2$, $p^* \propto 2\mu_1\mathbf{1} + \mu_2 c_2$ is an increasing affine image of $c_2$ when $\mu_2 > 0$, so the order of $p^*$ is that of $c_2$. For $n \ge 3$ the constraints prune the search but do not make it polynomial.

## Depends on

- [Multinomial read-depth model of a tumour genome mixture](multinomial-read-depth-model-of-a-tumour-genome-mixture.md)

## Sources

- L. Oesper, A. Mahmoody, B. J. Raphael, *THetA: inferring intra-tumor heterogeneity from high-throughput DNA sequencing data*, Genome Biology 14 (2013), R80, Materials and methods, "A more efficient algorithm for the MLMDP" (Theorem 2). <https://doi.org/10.1186/gb-2013-14-7-r80> (PMCID: PMC4054893)
