# Polynomial-time geodesics in tree space (Owen–Provan)

The Billera–Holmes–Vogtmann space $\mathcal T_n$ of phylogenetic trees is CAT(0), so any two trees $T$, $T'$ are joined by a unique geodesic (Owen and Provan 2011, Section 2.1, recalling Billera, Holmes and Vogtmann). For trees with no common edges, Owen and Provan describe candidate paths by supports $(\mathcal A, \mathcal B)$, partitions $A_1, \dots, A_k$ of the edges of $T$ and $B_1, \dots, B_k$ of the edges of $T'$, satisfying their conditions (P1) ($A_i$ compatible with $B_j$ for $i > j$) and (P2) (an ordering condition on the ratios $\|A_i\|/\|B_i\|$, where $\|\cdot\|$ is the Euclidean norm of the edge lengths). Theorem 2.5 states that such a proper path is the geodesic if and only if (P3) holds: no support pair $(A_i, B_i)$ admits nontrivial partitions $A_i = C_1 \cup C_2$ and $B_i = D_1 \cup D_2$ with $C_2$ compatible with $D_1$ and $\|C_1\|/\|D_1\| < \|C_2\|/\|D_2\|$. The GTP algorithm checks (P3) by solving an extension problem, a minimum-weight vertex cover in a bipartite incompatibility graph computed by max-flow, and by Theorem 3.5 it finds the geodesic in $O(n^4)$ time; common edges are handled at the end of Section 3 of the source.

## Expansion

1. Tree space, proper paths and their supports, and the length of a path in terms of $\|A_i\|$ and $\|B_i\|$.
2. Conditions (P1), (P2) and (P3), and the characterization Theorem 2.5.
3. The extension problem and its reduction to minimum-weight vertex cover in a bipartite graph, solved by max-flow.
4. The GTP algorithm, its correctness and the $O(n^4)$ bound (Theorem 3.5), with the reduction to trees without common edges.

## Sources

- M. Owen and J. S. Provan, A fast algorithm for computing geodesic distances in tree space, IEEE/ACM Trans. Comput. Biol. Bioinform. 8 (2011), 2–13, Theorems 2.5 and 3.5. <https://arxiv.org/abs/0907.3942>
