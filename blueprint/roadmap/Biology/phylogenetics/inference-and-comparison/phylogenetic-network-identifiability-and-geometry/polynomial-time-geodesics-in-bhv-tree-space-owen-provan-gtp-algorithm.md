# Polynomial-time geodesics in tree space (Owen–Provan)

The Billera–Holmes–Vogtmann [tree space](../../../not-yet-classified/phylogenetic-tree-space/tree-space.md) $\mathcal T_n$ with its [path-length distance](../../../not-yet-classified/phylogenetic-tree-space/bhv-dist.md) is [CAT(0)](../../../not-yet-classified/phylogenetic-tree-space/tree-space-is-cat0.md), so any two trees $T$, $T'$ are joined by a [unique geodesic](../../../not-yet-classified/phylogenetic-tree-space/tree-space-geodesic-unique.md) (Owen and Provan 2011, Section 2.2, recalling Billera, Holmes and Vogtmann). Owen and Provan give an algorithm that computes this geodesic.

Let $E$ and $E'$ be the sets of interior edges of $T$ and $T'$, and suppose first that the trees have no common edges. For an edge set $A$ write $\|A\|$ for the Euclidean norm of the vector of lengths of the edges in $A$. A support $(\mathcal A, \mathcal B)$ consists of partitions $A_1, \dots, A_k$ of $E$ and $B_1, \dots, B_k$ of $E'$ satisfying

- (P1) for each $i > j$, $A_i$ is compatible with $B_j$; and
- (P2) $\|A_1\|/\|B_1\| \le \|A_2\|/\|B_2\| \le \dots \le \|A_k\|/\|B_k\|$, with equality allowed.

Condition (P1) makes the orthants $\mathcal O(B_1 \cup \dots \cup B_i \cup A_{i+1} \cup \dots \cup A_k)$ form a path space, and a support satisfying (P1) and (P2) determines a proper path through it. By Theorem 2.3 the geodesic is a proper path for some support satisfying (P1) and (P2). Theorem 2.5 states that a proper path with support satisfying (P1) and (P2) is the geodesic if and only if (P3) holds: no support pair $(A_i, B_i)$ admits nontrivial partitions $A_i = C_1 \cup C_2$ and $B_i = D_1 \cup D_2$ with $C_2$ compatible with $D_1$ and $\|C_1\|/\|D_1\| < \|C_2\|/\|D_2\|$. Without the ordering inequality (P2), condition (P3) alone does not certify a geodesic. The GTP algorithm starts from the cone path, checks (P3) by solving an extension problem, a minimum-weight vertex cover in a bipartite incompatibility graph computed by max-flow, and refines the support while keeping (P1) and (P2) (Lemma 3.4); by Theorem 3.5 it finds the geodesic in $O(n^4)$ time. Section 4 extends the algorithm to trees with common edges, including leaf edges, by splitting both trees at the common edges, running the algorithm on each pair of disjoint subtrees, and moving the common edge lengths linearly.

## Depends on

- [Tree Space](../../../not-yet-classified/phylogenetic-tree-space/tree-space.md)
- [Bhv Dist](../../../not-yet-classified/phylogenetic-tree-space/bhv-dist.md)
- [The space of phylogenetic trees is CAT(0)](../../../not-yet-classified/phylogenetic-tree-space/tree-space-is-cat0.md)
- [Geodesics in tree space are unique](../../../not-yet-classified/phylogenetic-tree-space/tree-space-geodesic-unique.md)

## Expansion

1. Tree space, proper paths and their supports, and the length of a path in terms of $\|A_i\|$ and $\|B_i\|$.
2. Conditions (P1), (P2) and (P3), the representation of the geodesic by a support satisfying (P1) and (P2) (Theorem 2.3), and the characterization Theorem 2.5.
3. The extension problem and its reduction to minimum-weight vertex cover in a bipartite graph, solved by max-flow.
4. The GTP algorithm, preservation of (P2) (Lemma 3.4), its correctness and the $O(n^4)$ bound (Theorem 3.5).
5. The extension to common edges and leaf edges (Section 4).

## Sources

- M. Owen and J. S. Provan, A fast algorithm for computing geodesic distances in tree space, IEEE/ACM Trans. Comput. Biol. Bioinform. 8 (2011), 2–13, Sections 2.2–2.3 and 4, Theorems 2.3, 2.5 and 3.5. <https://arxiv.org/abs/0907.3942>
