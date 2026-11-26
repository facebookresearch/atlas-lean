# Single and multiple consensus trees under the parent-child distance

**Definitions.** A *mutation tree* is a rooted tree whose $m$ nodes are uniquely labelled by mutations $[m] = \{1, \dots, m\}$ (obtained from an infinite-sites phylogeny by contracting unlabelled edges). For rooted trees $T = (V, E)$ and $T' = (V, E')$ on the same vertex set, the *parent-child distance* is

$$d(T, T') = |E \setminus E'| + |E' \setminus E|,$$

a metric. Given input trees $\mathcal T = \{T_1, \dots, T_n\}$ on $V$, the *parent-child graph* $G_{\mathcal T}$ is the directed graph on $V$ containing every edge of every input tree, with weight $\ell(u,v) = |\{ i : (u,v) \in E_i \}|$.

- *Single Consensus Tree (SCT):* find a rooted tree $R$ on $V$ minimizing $d(\mathcal T, R) = \sum_i d(T_i, R)$.
- *Multiple Consensus Tree (MCT):* for $1 \le k \le n$, find a surjective clustering $\sigma : [n] \to [k]$ and trees $R_1, \dots, R_k$ minimizing $\sum_i d(T_i, R_{\sigma(i)})$.

**Results.**

1. Every spanning arborescence $R$ of $G_{\mathcal T}$ satisfies $d(\mathcal T, R) = 2\,[\,n(m-1) - \ell(R)\,]$, where $\ell(R)$ is its total weight. Hence some optimal SCT solution is a maximum-weight spanning arborescence of $G_{\mathcal T}$; in particular one can take every consensus edge to occur in some input tree, and every edge shared by all input trees to be in the consensus.
2. For a fixed clustering $\sigma$, MCT decomposes into $k$ independent SCT problems, one per cluster; the analogous edge properties hold cluster by cluster.
3. The optimal MCT cost is monotonically decreasing in $k$ (it is $0$ when $k = n$).
4. MCT is NP-hard.

## Expansion

Every rooted tree on $m$ vertices has $m - 1$ edges, so $d(T_i, R) = 2(m - 1) - 2|E_i \cap E_R|$; summing over $i$ gives $2[n(m-1) - \sum_{e \in E_R} \ell(e)]$, where edges absent from $G_{\mathcal T}$ contribute weight zero. Minimizing distance therefore means maximizing total weight over spanning arborescences, solvable for each choice of root by the Chu–Liu–Edmonds algorithm. Once the clustering is fixed, the objective is a sum over clusters, giving the decomposition, and splitting a cluster never increases the cost, giving monotonicity. NP-hardness reduces from Clique: each vertex of a graph $H$ becomes an input tree encoding its incident edges, and with $k - 1$ singleton clusters the cost reaches $2[(c-1)|E(H)| - \binom{c}{2}]$ exactly when the remaining cluster of $c$ trees encodes a clique. In practice, exact solutions come from an integer linear program with connectivity cuts and fast heuristics from coordinate ascent alternating clustering and arborescence steps, with the number of clusters chosen by a likelihood penalized for model complexity.

## Sources

- N. Aguse, Y. Qi, M. El-Kebir, "Summarizing the solution space in tumor phylogeny inference by multiple consensus trees", Bioinformatics (2019), Definitions 1–4 (Eqs. 1–2), Problems 1–2, Theorem 1 (maximum weight spanning arborescence), Lemmas 1–3, Proposition 1, Corollaries 1–3, Proposition 2, Theorem 2 (NP-hardness) with Lemmas 4–6, and the ILP (Eqs. 11–19). <https://doi.org/10.1093/bioinformatics/btz312> (PMC6612807).
