# Haplotype-aware colinear chaining with recombination penalty

Let $G(V,E,\sigma,H)$ be a haplotype-aware pangenome DAG as in [Complexity of haplotype-aware sequence-to-graph alignment](complexity-of-haplotype-aware-sequence-to-graph-alignment.md), now with sequence labels $\sigma : V \to \Sigma^+$. An anchor $M[i] = (v, [x..y], [c..d])$ records a match between the query substring $Q[c..d]$ and $\sigma(v)[x..y]$, and carries a user-specified weight $\mathrm{weight}(M[i])$; there are $N$ anchors $M[1..N]$. Write $R^-(v)$ for the set of vertices that can reach $v$ (including $v$).

**Precedence.** $M[i] \prec M[j]$ if $M[i].d < M[j].c$, $M[i].v \in R^-(M[j].v)$, and $M[i].y < M[j].x$ whenever $M[i].v = M[j].v$.

**Chain.** A chain is a sequence $S = (s_1,\dots,s_p)$ of pairs $s_j = (i_j, h_j)$ with $h_j \in \mathrm{haps}(M[i_j].v)$ and $M[i_j] \prec M[i_{j+1}]$; $r(S)$ counts the indices with $h_j \ne h_{j+1}$.

**Problem 4.** For a penalty $\gamma \ge 0$, find a chain maximizing

$$\sum_{j=1}^{p} \mathrm{weight}(M[i_j]) - \gamma\, r(S).$$

**Lemma 6 (algorithm).** After an $O(|E||H|)$ preprocessing of the graph, Problem 4 can be solved in $O(|H| N \log(|H| N))$ time.

**Lemma 7 (conditional lower bound).** For every constant $\epsilon > 0$ there is no algorithm solving Problem 4 in $O(|H|^{1-\epsilon} N + |H| N^{1-\epsilon})$ time unless SETH is false.

The gap-sensitive variant (Problem 5), which also subtracts a gap cost between consecutive anchors, admits the same $O(|H| N \log(|H|N))$ algorithm and the same lower bound.

## Depends on

- [Complexity of haplotype-aware sequence-to-graph alignment](complexity-of-haplotype-aware-sequence-to-graph-alignment.md)

## Expansion

Let $C(i,h)$ be the best score of a chain ending with anchor $i$ on haplotype $h$ and $C''(i) = \max_h C(i,h)$. Switching haplotype costs exactly $\gamma$, so $C(i,h) \ge C''(i) - \gamma$ (Lemma 5): any chain ending at $(i,h')$ can be relabelled to end on $h$ with at most one extra recombination. The algorithm uses the haplotype paths as a path cover, precomputes for each vertex and haplotype the last vertex of that haplotype that reaches it, and processes anchor endpoints in sorted order, maintaining one balanced search tree per haplotype that answers range-maximum queries in $O(\log N)$; the sort of $O(|H|N)$ endpoints dominates. The lower bound reduces Orthogonal Vectors: one vector set becomes haplotype paths through a gadget graph and the other a query with weighted anchors, so that a chain of score $2d + (n-1)d$ exists iff an orthogonal pair exists, and such a chain uses no recombination (Lemmas 8–11).

## Sources

- G. Chandra, D. Gibney, C. Jain, "Haplotype-aware sequence alignment to pangenome graphs", Genome Research 34(9) (2024) 1265–1275, Methods (Definitions 1–2, Problems 4–5, Lemmas 4–11), <https://doi.org/10.1101/gr.279143.124>, PMCID PMC11529843.
