# Hanan-grid reduction and an MST lower bound for tumour copy-number phylogenies

**Problem.** Let $S \subset \mathbb{Z}_{\ge 0}^d$ be the set of distinct copy-number patterns observed over $d$ probes. The weight of an edge between $x, y \in \mathbb{R}^d$ is the rectilinear distance $\|x - y\|_1 = \sum_{i=1}^d |x_i - y_i|$, the minimum number of single-gene gains and losses turning $x$ into $y$. A rectilinear Steiner minimum tree (RSMT) of $S$ is a tree of least total weight whose vertex set contains $S$ and possibly additional Steiner points. Observed patterns may be internal vertices (a sampled clone can be ancestral to another), which is why algorithms that require terminals to be leaves do not apply.

**Theorem (Hanan, Snyder).** For each $P \in S$ and axis $i$, let $N(P, i)$ be the hyperplane through $P$ orthogonal to axis $i$, and let $I_H(S)$ be the set of points $Q$ with $Q_i \in \{P_i : P \in S\}$ for every $i$ (the intersection points of the Hanan grid). There is an RSMT of $S$ all of whose Steiner points lie in $I_H(S)$.

Hence an exact algorithm enumerates subsets $T \subseteq I_H(S) \setminus S$ and returns the cheapest minimum spanning tree of $S \cup T$ under $\|\cdot\|_1$. With copy numbers in $\{0, \dots, m - 1\}$ there are at most $s = m^d$ candidates and the running time is $O(2^s\, n \log n)$.

**MST lower bound.** Let a weighted complete graph on nodes $1, \dots, n$ be such that only nodes $1, \dots, r$ can have degree $1$ in a minimum spanning tree (Steiner nodes of degree $1$ never reduce the weight, so they are excluded). With $w_v = \min_{u \ne v} w_{vu}$,

$$W(\mathrm{MST}) \;\ge\; \sum_{v=1}^{n} w_v - \max_{1 \le v \le r} w_v .$$

A candidate subset $T$ whose bound already exceeds the best tree found so far can be skipped without computing its MST.

## Expansion

Intuitively, Snyder's theorem extends Hanan's two-dimensional grid argument: in an optimal rectilinear tree any Steiner coordinate not shared with a terminal can be slid along its axis toward a terminal coordinate without increasing length, since the length is piecewise linear in that coordinate. For the lower bound, every tree has at least two leaves, and all leaves are among nodes $1, \dots, r$, so the MST can be rooted at some eligible node $\rho$. Each non-root node $v$ is joined to its parent by an edge of weight $p_v \ge w_v$, so $W(\mathrm{MST}) = \sum_{v \ne \rho} p_v \ge \sum_v w_v - w_\rho \ge \sum_v w_v - \max_{v \le r} w_v$. Restricting the maximum to eligible nodes is what makes the bound tight enough to prune most subsets in practice. Trees from the exact method or from a median-joining heuristic over Hanan-grid medians then yield statistics such as the subtree sizes below the root's children, which differ between primary tumours and their metastases.

## Sources

- S. A. Chowdhury, S. E. Shackney, K. Heselmeyer-Haddad, T. Ried, A. A. Schäffer, R. Schwartz, "Phylogenetic analysis of multiprobe fluorescence in situ hybridization data from tumor cell populations", Bioinformatics 29 (2013) i189–i198, Sections 2.1–2.5 (Theorems 1–3, Inequality (1), Algorithm 1), <https://doi.org/10.1093/bioinformatics/btt205> (PMC3694640).
