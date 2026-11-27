# Graph connectivity in O(log D + log log n) MPC rounds with sublinear memory

In the MPC model with strongly sublinear local memory $S = n^{\alpha}$ for any constant $\alpha \in (0, 1)$, the connected components of an $n$-vertex, $m$-edge graph whose components have diameter at most $D$ can be computed by a randomized algorithm with $O(m + n)$ total memory (isolated vertices included) in $O(\log D + \log\log_{b} n)$ rounds with high probability, without prior knowledge of $D$, where $b = \max\{2, m/n\}$ and every logarithm $\log x$ in a round bound is read as $\max\{1, \log x\}$, so that it stays positive for $D \le 1$, for sparse graphs such as a cycle ($m/n = 1$) and for $\log_b n < 2$. In detail, $O(\log D)$ rounds suffice when $D \ge \log^{\varepsilon} n$ for a constant $\varepsilon > 0$, and $O(\log\log_{b} n)$ rounds otherwise (Behnezhad-Dhulipala-Esfandiari-Łącki-Mirrokni). This improves the earlier $O(\log D \cdot \log\log_{b} n)$ rounds, with the same conventions, of Andoni-Song-Stein-Wang-Zhong.

## Proof sketch

Repeatedly expand each vertex's known neighbourhood by graph exponentiation while memory allows, until each vertex knows a ball of size proportional to its budget, then contract the graph by random leader election inside the known balls. Budgets are increased for vertices whose neighbourhoods are exhausted, so after $O(\log D)$ doubling steps the diameter is covered; a careful accounting of budgets and the growth of vertex degrees bounds the total memory and adds $O(\log\log n)$ rounds.

## Depends on

- [The massively parallel computation model](massively-parallel-computation-model.md)

## Sources

- A. Andoni, Z. Song, C. Stein, Z. Wang, P. Zhong, "Parallel Graph Connectivity in Log Diameter Rounds", FOCS 2018, arXiv:1805.03055.
- S. Behnezhad, L. Dhulipala, H. Esfandiari, J. Łącki, V. Mirrokni, "Near-Optimal Massively Parallel Graph Connectivity", FOCS 2019, arXiv:1910.05385, Theorem 1.
