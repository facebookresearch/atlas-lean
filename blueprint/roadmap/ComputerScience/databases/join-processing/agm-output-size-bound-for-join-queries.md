# AGM output-size bound for join queries

Let $Q = R_1 \bowtie \cdots \bowtie R_m$ be a full natural join query with hypergraph $H(Q)$ and let
$x = (x_e)$ be a fractional edge cover of $H(Q)$, that is, $x_e \ge 0$ and $\sum_{e \ni v} x_e \ge 1$ for
every attribute $v$. For every database $D$,

$$|Q(D)| \le \prod_{e} |R_e(D)|^{x_e}.$$

In particular $|Q(D)| \le |D|^{\rho^*(Q)}$, where $|D| = \sum_e |R_e(D)|$ is the total number of tuples and $\rho^*(Q)$ is the fractional edge cover number of
$H(Q)$.

## Sources

- A. Atserias, M. Grohe and D. Marx, *Size bounds and query plans for relational joins*, SIAM J. Comput. 42(4) (2013) 1737–1767, Lemma 2, §3.1. <http://www.cs.bme.hu/~dmarx/papers/atserias-sicomp2013-joins.pdf>
- H. Q. Ngo, E. Porat, C. Ré and A. Rudra, *Worst-case optimal join algorithms*, PODS 2012, arXiv:1203.1952, Theorem 3.1 (discrete Bollobás–Thomason inequality). <https://arxiv.org/pdf/1203.1952>
