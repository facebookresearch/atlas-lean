# Polynomial-time reconstruction of semi-directed level-1 networks from quarnets

**Setting.** A *semi-directed* phylogenetic network on leaf set $X$ is obtained from a rooted binary phylogenetic network by deleting the root and forgetting the direction of every tree edge, keeping only the directions of reticulation (hybrid) edges. It is *level-1* if every biconnected component (semi-directed cycle) contains at most one reticulation; its cycles may have three or more vertices. Its *quarnets* $\mathcal Q(N)$ are the semi-directed restrictions $N|_{Y}$ to all four-leaf subsets $Y\subseteq X$. An *$n$-sunlet* consists of a single semi-directed cycle of length $n$ with one leaf attached to each cycle vertex. A *square* is a 4-sunlet quarnet.

**Theorem.**

1. (Leaf insertion) For any ordering $x_1,\dots,x_n$ of the leaves of a level-1 network $N$ with $n\ge4$, $N$ is obtained from the base quarnet $N|_{\{x_1,\dots,x_4\}}$ by successive single-leaf attachments: to an edge, by creating a 3-cycle on an edge, or into an existing cycle.
2. (Unique optimal attachment) If $N=N'|_X$ with $|X|\ge4$ and $x\notin X$, there is a unique attachment of $x$ to $N$ that agrees with the quarnets $\mathcal Q(N')$. Hence the *sequential algorithm* reconstructs $N$ exactly from $\mathcal Q(N)$, in worst-case time $O(n^6)$.
3. (Sunlets) $N$ is an $n$-sunlet, $n\ge4$, iff $\mathcal Q(N)$ consists of $\binom{n-1}3$ squares and $\binom{n-1}4$ quartet trees. A sunlet, including the position of its reticulation, is recovered from its square quarnets alone.
4. (Cherries and exterior blobs) $N$ has a cherry $\{a,b\}$ iff exactly $\binom{n-2}2$ quarnets in $\mathcal Q(N)$ contain the cherry $\{a,b\}$, that is, every quarnet containing both $a$ and $b$. The leaf set of an exterior blob (a cycle attached to the rest of the network by a single non-trivial cut edge) is a color class of the greedy coloring of an incompatibility graph built from $\mathcal Q(N)$. The resulting *cherry-blob algorithm*, which repeatedly identifies and collapses tree cherries, reticulation cherries and exterior blobs, also returns $N$ from $\mathcal Q(N)$ in time $O(n^6)$.

## Expansion

Since level-1 semi-directed networks are encoded by their quarnets, the algorithmic question is how to assemble them efficiently. The sequential algorithm generalizes quartet puzzling. At each step it tries every candidate attachment of the new leaf and scores it against the $O(n^3)$ quarnets containing that leaf; uniqueness of the best-scoring attachment rests on the leaf-insertion decomposition. The cherry-blob algorithm mirrors cherry picking on trees. Exterior structures are detected purely from quarnet counts, and each is replaced by a single leaf, which reduces the problem size. For an exterior blob, the sunlet characterization fixes the cyclic order and the reticulation, since restricting a blob's support plus one outside leaf gives a sunlet. Both algorithms need the complete quarnet set; with estimated quarnets, as from concordance factors under the network multispecies coalescent, they become heuristics whose correctness depends on how accurately the quarnets are inferred.

## Sources

- Sophia Huebler, Rachel Morris, Joseph Rusinko, "Constructing Semi-Directed Level-1 Phylogenetic Networks from Quarnets", arXiv:1910.00048 (2019), Section 2 (semi-directed networks, quarnets, blobs), Theorems 1–4 (sequential algorithm), Theorems 5–11 and Corollary 1 (sunlets, exterior structures, cherry-blob algorithm), <https://doi.org/10.48550/arXiv.1910.00048>.
