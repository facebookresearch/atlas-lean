# History subpartition DAG

**Definitions.** Fix a label set $Y$ (for example all nucleotide sequences of a fixed length). Let $\mathrm{Part}(Y)$ be the family consisting of $\emptyset$ and of every collection $U$ of at least two pairwise disjoint nonempty subsets (clades) of $Y$. A **history sDAG** on $Y$ is a directed graph $(V, E)$ with
- $V \subseteq (Y \times \mathrm{Part}(Y)) \cup \{\rho\}$, where $\rho$ is a universal ancestor node; for $v = (\ell, U) \ne \rho$ its **clade union** is $\mathrm{CU}(v) = \{\ell\}$ if $U = \emptyset$ and $\bigcup_{C \in U} C$ otherwise;
- every node reachable from $\rho$, and $\rho$ with no incoming edge;
- for every edge $((\ell_1, U_1), v_2)$ with parent $\ne \rho$, $\mathrm{CU}(v_2) \in U_1$ (the edge descends from the node-clade pair $((\ell_1,U_1), \mathrm{CU}(v_2))$);
- for every node $v = (\ell, U)$ and every $C \in U$, at least one edge descending from $(v, C)$.

A **history** is a history sDAG in which $\rho$ has exactly one child and every node-clade pair has exactly one descending edge. Histories are in bijection with isomorphism classes of rooted, multifurcating, non-unifurcating trees whose nodes, internal ones included, carry labels in $Y$, with distinct labels on distinct leaves (the leaf labelling is injective; internal labels may repeat). Without this condition a root with two leaves both labelled $a$ would need two distinct leaf nodes, while the history sDAG has only the one node $(a, \emptyset)$.

**Lemma (structure).**
1. In a history sDAG the leaf labels reachable from $v$ are exactly $\mathrm{CU}(v)$.
2. A history sDAG is a history if and only if it is a tree with exactly one edge leaving $\rho$.
3. Every history sDAG is acyclic.
4. The graph union of two history sDAGs on $Y$ is a history sDAG; hence a collection $T$ of histories determines the history sDAG $\big(\bigcup_{t} V_t, \bigcup_t E_t\big)$, whose set of contained histories $D(T)$ satisfies $T \subseteq D(T)$.
5. A history sDAG is the history sDAG constructed from the set of histories it contains.

## Expansion

Along any edge the clade union can only shrink, $\mathrm{CU}(v_2) \in U_1$ implies $\mathrm{CU}(v_2) \subseteq \mathrm{CU}(v_1)$, and it shrinks strictly because a nonempty subpartition has at least two disjoint nonempty clades; so no directed cycle exists. Choosing one descending edge for every node-clade pair, starting from one child of $\rho$, carves out a tree, which is a history; conversely a history has one child per clade and cannot contain two paths to one node because sibling clades are disjoint. Storing subpartitions on nodes is what makes the union operation faithful: two tree nodes with the same label but different child clades stay distinct. The union usually contains strictly more histories than were used to build it, obtained by swapping subhistories below nodes that share label and subpartition, which is how the structure compactly represents large ensembles of maximum-parsimony trees, for example of SARS-CoV-2 or B-cell lineage sequences.

## Sources

- W. Dumm, M. Barker, W. Howard-Snyder, W. S. DeWitt III, F. A. Matsen IV, "Representing and extending ensembles of parsimonious evolutionary histories with a directed acyclic graph", Journal of Mathematical Biology 87 (2023) 75, Definitions 1-8 and Lemmas 3-8, <https://doi.org/10.1007/s00285-023-02006-3>, PMCID PMC10600060.
