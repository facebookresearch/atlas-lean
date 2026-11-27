# Genus additivity and the grammar of 0-structures over two backbones

**Definitions.** A diagram over $b$ backbones is a set of arcs on $b$ horizontally placed, oriented backbones; for two RNA strands $R$ (first) and $S$, arcs may join two vertices of one strand or one vertex of $R$ with one of $S$ (interaction arcs). Its genus $g$ is the genus of the oriented surface of its fatgraph. A **stack** is a maximal set of parallel arcs $(i,j),(i+1,j-1),\dots$; a **shadow** is a diagram with no non-crossing arcs and no isolated vertices in which every stack has size one. A diagram is **irreducible** if it is connected and any two arcs are linked by a chain of pairwise crossing arcs. For a diagram $X$, an irreducible $X$-shadow is an irreducible shadow all of whose arcs lie in $X$. $X$ is a **$\gamma$-structure** if every irreducible $X$-shadow has genus at most $\gamma$. The gluing map $\alpha$ sends a diagram $E$ over two backbones to the diagram over one backbone obtained by joining the $3'$ end of $R$ to the $5'$ end of $S$. Split the irreducible $E$-shadows into $\mathbb{I}_1(E)$ (those over one backbone) and $\mathbb{I}_2^i(E)$ (those over two backbones with $g(\alpha(S')) = g(S') + i$, $i \in \{0,1\}$).

**Theorem.**

1. (Finiteness) A shadow of genus $g \ge 1$ over two backbones has between $2g+1$ and $6(g+1) - 2$ arcs, and one of genus $0$ has between $2$ and $4$ arcs; every intermediate arc count is attained, also by irreducible shadows. In particular there are finitely many (irreducible) shadows of each genus, and exactly seven non-trivial shadows over two backbones have genus $0$.
2. (Genus additivity) If $E$ is a $\gamma$-structure over two backbones, then

$$g(E) = \begin{cases} \displaystyle\sum_{S' \in \mathbb{I}_1(E)} g(S') + \sum_{S' \in \mathbb{I}_2^0(E)} g(S') + \sum_{S' \in \mathbb{I}_2^1(E)} \big(g(S') + 1\big), & \mathbb{I}_2^0(E) \ne \emptyset,\\[2ex] \displaystyle\sum_{S' \in \mathbb{I}_1(E)} g(S') + \sum_{S' \in \mathbb{I}_2^1(E)} \big(g(S') + 1\big) - 1, & \mathbb{I}_2^0(E) = \emptyset. \end{cases}$$

3. (Grammar) There is a grammar $\mathscr{G}_0$ such that every $0$-structure over two backbones decomposes uniquely via $\mathscr{G}_0$ and every diagram it generates is a $0$-structure over two backbones. $\mathscr{G}_0$ is unambiguous, so it computes the partition function, base-pairing probabilities, probabilities of hybrid blocks and gap structures, and Boltzmann samples of $0$-structures over two backbones, with $O(n^6)$ time and $O(n^4)$ space for the partition function.

Because a $0$-structure is built from finitely many genus-$0$ irreducible shadows yet may have arbitrarily high total genus, this class strictly contains the joint structures of earlier interaction models and includes, e.g., two crossing hybrids.

## Expansion

Contracting non-crossing arcs, isolated vertices and stacks does not change the fatgraph genus, so every diagram projects to a shadow. Euler's formula $2 - 2g = v - e + r$ for the fatgraph, together with the fact that every boundary component of a shadow (other than those through the backbone ends) has length at least three, bounds the number of arcs linearly in $g$; the two-backbone bounds follow by gluing the backbones with $\alpha$, which raises the genus by at most one. The genus of $\alpha(E)$ is additive over its irreducible components; subtracting the contribution of the gluing, which raises the genus by one exactly when no two-backbone component absorbs it, gives the two-case formula. With only seven genus-$0$ two-backbone shadows, the grammar inflates each into stacks, gaps and secondary structures, and the most expensive production has six free indices over the two strands.

## Sources

- Jørgen E. Andersen, Fenix W.D. Huang, Robert C. Penner, Christian M. Reidys, "Topology of RNA-RNA Interaction Structures", Journal of Computational Biology 19 (2012), 928–943, <https://doi.org/10.1089/cmb.2011.0308>. Published version of arXiv:1112.6194, cited next; locators there refer to the arXiv version.
- Jørgen E. Andersen, Fenix W. D. Huang, Robert C. Penner, Christian M. Reidys, "Topology of RNA-RNA interaction structures", arXiv (2011). Definitions 1–4, Theorem 1, Corollaries 1–3, Lemma 1, Lemma 2, Theorem 2. <https://doi.org/10.48550/arXiv.1112.6194>
