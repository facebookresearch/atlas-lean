# Locality-sensitive hashing index with L tables and a stopping rule

Let $\mathcal{H}$ be an $(r, cr, p_1, p_2)$-sensitive family and let $g = (h_1, \dots, h_k)$ be the AND of $k$ independent functions of $\mathcal{H}$, which is $(r, cr, p_1^k, p_2^k)$-sensitive. The *LSH index* stores $L$ hash tables keyed by independent draws $g_1, \dots, g_L$. A query $q$ lists the points of $P$ colliding with $q$ in table $1$, then table $2$, and so on, examines at most the first $T$ of these candidates, and returns the first one within distance $cr$ of $q$, or nothing. The standard parameters are

$$
\rho = \frac{\ln(1/p_1)}{\ln(1/p_2)}, \quad k = \left\lceil \log_{1/p_2} |P| \right\rceil, \quad L = \left\lceil |P|^\rho / p_1 \right\rceil, \quad T = 3L .
$$

## Depends on

- [Approximate near-neighbour problem](approximate-near-neighbor-problem.md)
- [Locality-sensitive hash families](../locality-sensitive-hashing/locality-sensitive-hash-families.md)
- [Amplification of locality-sensitive families by banding](../locality-sensitive-hashing/amplification-of-locality-sensitive-families-by.md)

## Sources

- P. Indyk and R. Motwani, "Approximate Nearest Neighbors: Towards Removing the Curse of Dimensionality", Proceedings of the 30th ACM Symposium on Theory of Computing (STOC), 1998.
- S. Har-Peled, P. Indyk and R. Motwani, "Approximate Nearest Neighbor: Towards Removing the Curse of Dimensionality", Theory of Computing 8(14), 2012.
