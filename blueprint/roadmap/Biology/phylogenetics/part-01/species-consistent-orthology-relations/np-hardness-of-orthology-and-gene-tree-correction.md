# NP-hardness of orthology and gene tree correction

Use the definitions of DS-trees, $S$-consistency, relation graphs and $P_3(R)$ from [Triplet characterization of species-consistent relation graphs](triplet-characterization-of-species-consistent-relation-graphs.md).

**Minimum Edge-Removal Consistency.** Given a relation graph $R$, a species tree $S$ and an integer $k$, decide whether there is an $S$-consistent spanning subgraph $R'$ ($V(R') = V(R)$) with $|E(R) \setminus E(R')| \le k$.

**Theorem 3.** Minimum Edge-Removal Consistency is NP-complete, even when the genes belong to pairwise distinct species.

**Maximum Node Consistency.** Given $R$, $S$ and $k$, decide whether $R$ has an $S$-consistent induced subgraph with at least $k$ vertices.

**Theorem 4 and Corollary 1.** For every $0 < \varepsilon < 1$ and constant $d > 0$, the optimization version of Maximum Node Consistency cannot be approximated within a factor $d\,n^{\frac12(1-\varepsilon)}$, where $n = |V(R)|$ (unless P = NP); its decision version is NP-hard. Both hold even when genes belong to pairwise distinct species.

**Gene tree correction.** Given a species tree $S$, an $S$-consistent DS-tree $G$ and orthology/paralogy constraints, find an $S$-consistent DS-tree $G'$ inducing the constraints that is closest to $G$.

**Theorem 5.** Maximum Homology Correction (maximize the number of orthology/paralogy relations of $G$ preserved in $G'$) is NP-complete, even when $S$, $G$ and $G'$ are binary.

**Theorem 6.** Maximum Clade Correction (maximize the number of clades shared by $G$ and $G'$, equivalently minimize their Robinson–Foulds distance) is NP-complete, even when $S$, $G$ and $G'$ are binary.

## Depends on

- [Triplet characterization of species-consistent relation graphs](triplet-characterization-of-species-consistent-relation-graphs.md)
- [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Proof depends on

- [EXACT COVER BY 3-SETS is NP-complete](../../../../TheoryOfComputation/np-completeness/set-systems-and-location/exact-cover-by-3-sets/exact-cover-by3-sets-np-complete.md)
- [INDEPENDENT-SET is NP-hard](../../../../TheoryOfComputation/np-completeness/graph-covering-and-domination/clique-independent-set-and-vertex-cover/part-08/ind-set-dec-np-hard.md)

## Expansion

Membership in NP uses Theorem 2 of the dependency: $S$-consistency of a candidate graph is checked by listing $P_3(R')$ and testing each triplet against $S$. Theorem 3 is a reduction from exact cover by 3-sets, in which the components of an optimal edge-reduced graph correspond to the chosen disjoint 3-sets. Theorem 4 is a gap-preserving reduction from Maximum Independent Set on an $m$-vertex graph to an instance with $n = m^2$ vertices, in which two large retained blocks may not be joined by an edge without inducing a forbidden triplet (Lemma 3). Theorem 5 reduces from Minimum Edge-Removal Consistency with one gene per genome (Theorem 3), and Theorem 6 from Maximum Node Consistency (Corollary 1), using that a gene can always be grafted onto an $S$-consistent tree as an ortholog of a chosen gene in another species while keeping all existing relations and $S$-consistency (Lemma 5). Hence exact correction of either the relations or the tree must rely on exponential algorithms or heuristics.

## Sources

- M. Lafond, R. Dondi, N. El-Mabrouk, "The link between orthology relations and gene trees: a correction perspective", Algorithms for Molecular Biology 11 (2016) 4, Theorems 3–6, Corollary 1, Lemmas 3–5, <https://doi.org/10.1186/s13015-016-0067-7>, PMCID PMC4833969.
