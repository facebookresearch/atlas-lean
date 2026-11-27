# Cover characterizations of tree-based, tree-child and tree-sibling networks

**Setting.** A rooted phylogenetic network on leaves $[n]$ is *labellable* if no two non-leaf vertices have the same set of children; labelling parents in a canonical order by $n+1,\dots,m$ turns it into its *cover* $\mathcal C$, the collection of children-label sets of all non-leaf vertices, the root included, a family of subsets of $[m]$ whose union is $[m]$. Labellable networks are in bijection with *expanding covers*: covers of $[m]$ in which, with $n=m-|\mathcal C|+1$, no element of $[n]$ appears twice and, for each $i=1,\dots,|\mathcal C|$, at least $i$ sets lie in $[n+i-1]$. An integer appearing in two or more sets is a reticulation. A partition $\pi$ of $[m]$ *embeds* in $\mathcal C$ if some injective map sends each block $A\in\pi$ to a set $A'\in\mathcal C$ with $A\subseteq A'$, and *fully embeds* if moreover $|\pi|=|\mathcal C|$.

**Theorem.** Let $\mathcal C$ be an expanding cover and $N$ its network.

1. *Tree-based.* $N$ is tree-based (obtained from a spanning tree with the same leaves by adding arcs) iff $\mathcal C$ has a fully embedded partition; full embeddings are in bijection with support trees of $N$.
2. *Counting support trees.* If $N$ is binary and tree-based, the number of support trees equals $2^c\prod_{f\in\mathcal F}(r(f)+1)$ (and $2^c$ if $\mathcal F=\emptyset$), where $c$ is the number of crowns (cyclic zig-zag trails) and $\mathcal F$ the set of fences, $r(f)$ the number of repeated integers in fence $f$.
3. *Tree-child.* $N$ is tree-child (every non-leaf vertex has a non-reticulate child) iff each set of $\mathcal C$ contains an integer appearing exactly once in $\mathcal C$; equivalently, every set containing a repeated integer also contains a once-appearing integer.
4. *Tree-sibling.* $N$ is tree-sibling (every reticulation is a sibling of a tree vertex) iff every repeated integer lies in at least one set that also contains a once-appearing integer.
5. *Normal.* For a tree-child cover in labelling order, $N$ is normal (tree-child without shortcuts) iff no *backtrack* for any $x$ (a chain of sets following labels from a set containing $x$ back towards the root) contains a set containing $x$.
6. *Spinal.* $N$ is *spinal* if it has a spine, a path from a leaf to the root through every non-leaf vertex; this holds iff $\mathcal C$ has exactly $i$ subsets of $[n+i-1]$ for each $i$.

Orchard networks are recognized from the cover by a cherry-reduction algorithm acting directly on its sets.

## Expansion

Each set of the cover is the children of one vertex, and an integer occurring in several sets is a vertex with several parents. Choosing for every reticulation one of its occurrences (deleting the others) yields a partition embedded in the cover, and this partition has as many blocks as the cover exactly when every parent keeps at least one child, which is the condition that the chosen arcs form a spanning tree with the original leaves, i.e. a support tree. A set containing an integer that appears only once is a vertex with a tree child, giving the tree-child condition; in the binary tree-child case each of the $k$ reticulations can independently keep either parent, recovering the count $2^k$ of support trees. Shortcuts (an arc parallel to a directed path) appear in the cover as a backtrack that returns to a set containing the starting element.

## Sources

- Andrew Francis, Daniele Marchei and Mike Steel, "Phylogenetic network classes through the lens of expanding covers", Journal of Mathematical Biology 88 (2024), 58, <https://doi.org/10.1007/s00285-024-02075-y>; numbering as in arXiv:2306.06519: Definition 2.1, Theorems 2.2, 3.2, 3.6, 4.1, 6.2, 6.3, 8.1, Corollaries 3.3, 4.5, 5.3 and Section 7 (orchard networks).
