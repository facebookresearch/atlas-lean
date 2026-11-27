# Minimum-reticulation galled networks by compatible subsets and attachment

**Setting.** Let $\mathcal C$ be a set of clusters on taxa $\mathcal X$ whose incompatibility graph is connected (P1) and in which every pair of taxa is separated by some cluster (P2). A galled network for $\mathcal C$ with few reticulations is built as a backbone tree plus reticulated taxa.

**Step 1: Maximum Compatible Subset (MCS).** Find a minimum set $R \subsetneq \mathcal X$ of taxa whose removal makes the restricted clusters $\mathcal C|_{\mathcal X \setminus R} = \{C \setminus R\}$ pairwise compatible; the taxa in $R$ become the reticulations.

- *Hardness.* MCS is NP-hard even restricted to inputs with properties (P1) and (P2).
- *Seed-growing algorithm.* Encode each incompatibility of two clusters $A, B$ as the triple $(A \cap B,\ A \setminus B,\ B \setminus A)$; removing all taxa of any one part resolves it. Keep candidate removal sets (seeds) with a rank counting how many incompatibilities in a fixed order they resolve; repeatedly take a minimum-size seed of maximum rank, advance its rank if it resolves the next incompatibility, and otherwise replace it by its three unions with the parts of that incompatibility. If the optimum has $k$ taxa, at most $3^{k+1}$ seeds are generated and the running time is $O(k\, |H|\, 3^k)$, where $H$ is the list of incompatibilities; the first seed reaching full rank is optimal.

**Step 2: Minimum Attachment (MAT).** Let $T$ be the rooted tree representing $\mathcal C|_{\mathcal X \setminus R}$ and $B$ the bottom part containing one node $v(r)$ per $r \in R$ (plus nodes for clusters of taxa in $R$). Choose a minimum set of link edges from $T$ to $B$ such that (A1) for every edge $e$ of $T$ and every taxon $r$ required by a cluster mapped to $e$, $v(r)$ is reachable from below $e$; (A2) every non-singleton bottom node receives exactly one link; (A3) $v(r)$ is reachable avoiding $e$ whenever some cluster mapped to $e$ excludes $r$. Deciding whether a solution with at most $k$ links exists is NP-complete (and W[2]-hard in $k$), so it is solved by branch and bound or integer linear programming in practice.

## Depends on

- [Galled networks and efficient softwired cluster containment](galled-networks-and-efficient-softwired-cluster-containment.md)

## Expansion

Every incompatibility must be destroyed by removing one of its three parts, which gives the branching factor three and the $3^{k+1}$ bound on the enumeration tree of seeds; choosing minimum-size seeds first makes the first complete seed optimal, so the method is exact, not greedy. MCS hardness reduces from the problem of removing $k$ taxa to make a general cluster set compatible (equivalent to the maximum compatible tree problem) by adding an outgroup taxon and auxiliary clusters that enforce (P1) and (P2). MAT hardness reduces from set cover: one auxiliary taxon and a caterpillar-like tree encode the sets, and $m + k$ links suffice iff $k$ sets cover the universe. Each connected component of the incompatibility graph is processed separately, which keeps instances small enough that exact solutions are found in seconds on data sets with hundreds of taxa, such as 279 prokaryotes from nine gene trees.

## Sources

- D. H. Huson, R. Rupp, V. Berry, P. Gambette, C. Paul, "Computing galled networks from real data", Bioinformatics (2009), Section 4 (MCS problem, incompatibility statements, Lemmas 2–3, seed-growing algorithm), Section 5 (properties A1–A3, Problem 3, Lemma 4) and Appendix A (proofs of Lemmas 2–4). <https://doi.org/10.1093/bioinformatics/btp217> (PMC2687971).
