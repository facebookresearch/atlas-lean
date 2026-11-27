# Super-reconciliation of synteny trees

**Syntenies and events.** Let $\mathcal F = \{\Gamma_1, \dots, \Gamma_t\}$ be gene families. A **synteny** is an ordered sequence $X = g_1 g_2 \cdots g_k$ of genes of one genome, each from a different family. A **segmental duplication** $\mathrm{Dup}(X, [i,j])$ creates a copy of the substring $g_i \cdots g_j$ (partial if $[i,j] \ne [1,k]$). A **segmental loss** $\mathrm{Loss}(X,[i,j])$ deletes $g_i\cdots g_j$; it is a full loss (fLoss) if nothing remains and a partial loss (pLoss) otherwise. Given gene trees $T_1, \dots, T_t$ (one per family) whose genes are organized into a set $\mathcal X$ of extant syntenies, the **synteny tree** $\tilde T_i$ relabels each leaf of $T_i$ by its synteny. A **super-reconciliation** $R(\mathcal G, S)$ with a species tree $S$ is a labelled synteny tree extending every $\tilde T_i$ that is a valid history for $\mathcal X$ under speciations, segmental duplications and losses; its cost is the number of Dup, fLoss and pLoss events.

**Existence.**
1. $\mathcal X$ is **order consistent** (has an ancestral gene order from which every synteny arises by losses) iff its precedence graph on gene families is acyclic; then every topological sort is an admissible ancestral synteny.
2. If a super-reconciliation exists, the synteny trees $\tilde T_1, \dots, \tilde T_t$ are consistent (they agree on every triplet of syntenies they share). If they are consistent, every super-reconciliation extends a supertree of $\{\tilde T_i\}$, and every supertree is the backbone of some super-reconciliation.

**Complexity.** Minimizing the number of segmental duplications is NP-hard and cannot be approximated within $n^{1-\epsilon}$ for any $0 < \epsilon < 1$ ($n$ the number of syntenies); minimizing the full Dup + fLoss + pLoss cost is NP-hard.

**Dynamic program on a fixed supertree.** Let $D_T(X,Y)$ (respectively $D_P(X,Y)$) be the minimum number of segmental losses turning $X$ (respectively a substring of $X$) into its subsequence $Y$, and $d(v, X)$ the minimum cost below node $v$ of the LCA-reconciled supertree when $v$ carries synteny $X$. Then $d(v,X) = 0$ at the leaf carrying $X$ and $+\infty$ at other leaves; at a speciation

$$d(v,X) = \min_{X_l \subseteq X}\big(D_T(X,X_l) + d(v_l,X_l)\big) + \min_{X_r \subseteq X}\big(D_T(X,X_r) + d(v_r,X_r)\big);$$

at a duplication the cost is $1$ plus the better of the two assignments in which one child receives the full copy (charged with $D_T$) and the other a duplicated substring (charged with $D_P$). Ignoring gene order, the minimum cost of the unordered problem is computable in $O(|V(\tilde T)|\,|\mathcal F|)$ time.

## Depends on

- [Multi-gene reconciliation with segmental duplications](multi-gene-reconciliation-with-segmental-duplications.md)
- [Topological order](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/topological-sorting/is-topological-order.md)

## Expansion

Gene order can only shrink along a lineage (losses delete substrings; duplications create new syntenies but leave the old one intact), so an ancestral order must be a common supersequence compatible with all observed precedences, hence the acyclicity test. Because every family's tree is displayed by the history, the history's synteny skeleton is a supertree, and conversely losses can always be grafted to make any supertree a valid history. On a fixed supertree the event type of each internal node is forced by the LCA mapping (a node whose children map to non-separated species must be a duplication), which leaves only the synteny labels to optimize and yields the recursion. The approach trades independent per-family duplications for fewer, larger segmental events, which is the realistic explanation when several genomic regions share gene content and order.

## Sources

- M. Delabre, N. El-Mabrouk, K. T. Huber, M. Lafond, V. Moulton, E. Noutahi, M. S. Castellanos, "Evolution through segmental duplications and losses: a Super-Reconciliation approach", Algorithms for Molecular Biology 15:12 (2020), Definitions 1–2, Lemmas 1–4, Theorems 1–5, <https://doi.org/10.1186/s13015-020-00171-4>, PMCID PMC7249433.
