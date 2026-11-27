# Counting multi-target RNA designs is #P-hard

Let $G = (V_1 \cup V_2, E)$ be a connected bipartite **base-pair dependency graph** (positions as vertices, base pairs of the target structures as edges). A **design** assigns nucleotides so that every edge receives a canonical pair in $\mathcal{B} = \{\{A,U\},\{G,C\},\{G,U\}\}$. Fixing one nucleotide in a connected component fixes the purine/pyrimidine class of all its positions, so up to the symmetry $A \leftrightarrow C$, $G \leftrightarrow U$ one may restrict $V_1$ to $\{A,G\}$; call these restricted designs $\mathrm{Designs}^\star(G)$, so $\#\mathrm{Designs}(G) = 2\,|\mathrm{Designs}^\star(G)|$.

**Proposition.** $|\mathrm{Designs}^\star(G)| = |\mathrm{IndSets}(G)|$, the number of independent sets of $G$, via the bijection $f \mapsto \{v : f(v) \in \{A, C\}\}$.

**Corollary.** Counting valid designs, and hence computing the design partition function, is #P-hard even when the dependency graph is bipartite and connected; a polynomial-time algorithm would imply $\#P = FP$.

Moreover, among the $4^m$ assignments of $m$ positions forming a connected component of the base-pair dependency graph, at most $2^m$ respect pairing rules, which prunes the dynamic programme.

## Depends on

- [Treewidth-parameterized Boltzmann sampling of multi-target RNA designs](treewidth-parameterized-boltzmann-sampling-of-multi-target-rna-designs.md)

## Expansion

With $V_1 \subseteq \{A,G\}$ and $V_2 \subseteq \{C,U\}$, an edge between $v_1 \in V_1$ and $v_2 \in V_2$ fails to be canonical only for the pair $\{A, C\}$. So the set of positions carrying $A$ or $C$ must contain no edge, i.e. be an independent set, and every independent set $I$ arises from the assignment $A$ on $V_1 \cap I$, $C$ on $V_2 \cap I$, $G$ on $V_1 \setminus I$, $U$ on $V_2 \setminus I$. Since counting independent sets in connected bipartite graphs (#BIS) is #P-hard, so is counting designs. This explains why the treewidth parameterization, exponential in the worst case, is the natural tractable regime.

## Sources

- S. Hammer, W. Wang, S. Will and Y. Ponty, "Fixed-parameter tractable sampling for RNA design with multiple target structures", BMC Bioinformatics 20 (2019), Proposition 1 and its consequences, <https://doi.org/10.1186/s12859-019-2784-7>, PMCID: PMC6482512.
