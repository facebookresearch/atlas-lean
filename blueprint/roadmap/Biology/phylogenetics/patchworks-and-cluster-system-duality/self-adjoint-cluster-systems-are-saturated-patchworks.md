# Self-adjoint cluster systems are saturated patchworks

Let $X$ be a finite set of taxa and $\mathcal C(X)$ the set of nonempty subsets of $X$; a **cluster system** is any $\mathcal C \subseteq \mathcal C(X)$. Two sets $A,B$ are **compatible**, $A \parallel B$, if $A \cap B \in \{\emptyset, A, B\}$. A **hierarchy** is a cluster system whose clusters are pairwise compatible (the cluster system of a rooted phylogenetic tree). The **adjoint** $\mathcal C^*$ is the set of all $A \in \mathcal C(X)$ compatible with every cluster of $\mathcal C$; $\mathcal C \mapsto \mathcal C^*$ is a Galois connection, so $\mathcal C \subseteq \mathcal C^{**}$ and $\mathcal C = \mathcal C^{**}$ iff $\mathcal C = \mathcal A^*$ for some $\mathcal A$. Write $\mathcal C_{\mathrm{triv}} = \{C : |C| = 1 \text{ or } C = X\} = \mathcal C(X)^*$.

A cluster system $\mathcal C$ is

- a **patchwork** if $A, B \in \mathcal C$, $A \nparallel B$ imply $A \cap B,\ A \cup B \in \mathcal C$;
- a **weak patchwork** if $A, B \in \mathcal C$, $A \nparallel B$ imply $A \cup B \in \mathcal C$;
- a **saturated patchwork** if $A, B \in \mathcal C$, $A \nparallel B$ imply $A \cap B,\ A \cup B,\ A - B,\ B - A,\ (A \cup B) - (A \cap B) \in \mathcal C$;
- **ample** if $C_1 - C_2 \in \mathcal C$ for every arc $(C_2, C_1)$ of its Hasse diagram.

**Theorem (self-adjoint systems).** $\mathcal C = \mathcal C^{**}$ (equivalently, $\mathcal C$ is the adjoint of some cluster system) if and only if $\mathcal C$ is a saturated patchwork containing $\mathcal C_{\mathrm{triv}}$. In particular $\mathcal C^{**} = \mathcal C \cup \mathcal C_{\mathrm{triv}}$ for every saturated patchwork, and a hierarchy $\mathcal H$ satisfies $\mathcal H^{**} = \mathcal H$ iff $\mathcal H \supseteq \mathcal C_{\mathrm{triv}}$.

**Theorem (hierarchies via adjoints).** $\mathcal C$ is a hierarchy if and only if $\mathcal C^*$ is ample, in which case $\mathcal C^*$ is an ample saturated patchwork containing $\mathcal C_{\mathrm{triv}}$. Conversely, the adjoint of any ample weak patchwork containing $\mathcal C_{\mathrm{triv}}$ is a hierarchy.

**Proposition (structure and count).** $\mathcal C$ is an ample saturated patchwork containing $\mathcal C_{\mathrm{triv}}$ iff there is a (unique) hierarchy $\mathcal H \supseteq \mathcal C_{\mathrm{triv}}$, namely $\mathcal H = \mathcal C^*$, such that $\mathcal C$ is the disjoint union of $\{X\}$ and, for each $A \in \mathcal H$ with $|A| \ge 2$, the nonempty proper unions of the maximal proper subclusters of $A$ in $\mathcal H$. Then

$$|\mathcal C| = 1 + \sum_{A \in \mathcal C^*,\ |A| > 1} \big(2^{|\mathrm{Max}(\mathcal H : A)|} - 2\big).$$

## Expansion

The adjoint of any cluster system is a saturated patchwork containing the trivial clusters: if $C$ is compatible with two incompatible clusters $A, B$, a case check shows $C$ lies in, contains, or avoids each of $A \cup B$, $A \cap B$, $A - B$, $B - A$ and their symmetric difference, so these are all compatible with $C$ as well. For the converse, a saturated patchwork decomposes along its maximal proper subclusters: below each cluster $A$ either the maximal subclusters are pairwise disjoint or any two of them intersect and cover $A$, and saturation forces the second case to contain all unions of the atoms involved. This exhibits $\mathcal C$ as the double adjoint of the hierarchy of atoms. The characterization of hierarchies uses that a weak patchwork containing $\mathcal C_{\mathrm{triv}}$ is ample iff every sub-hierarchy extends within it to a maximal (binary) $X$-hierarchy.

## Sources

- Andreas Dress, Vincent Moulton, Mike Steel, Taoyang Wu, "On Patchworks and Hierarchies", arXiv (2012). Section 2 (definitions, facts (F0)–(F6)), Section 3 (patchwork conditions), Section 4 (Lemma 4.1, Proposition 4.2), Section 5 (Theorem 1, Proposition 5.1), Section 6 (Lemma 6.1, Theorem 2, Proposition 6.2). <https://doi.org/10.48550/arXiv.1202.2460>
