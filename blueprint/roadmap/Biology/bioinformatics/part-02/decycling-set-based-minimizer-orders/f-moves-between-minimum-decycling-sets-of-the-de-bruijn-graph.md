# F-moves between minimum decycling sets of the de Bruijn graph

**Window guarantees and decycling sets.** Let $D_k$ be the de Bruijn graph of order $k$ over an alphabet $\Sigma$ of size $\sigma$: its nodes are the $\sigma^k$ $k$-mers, with an edge $x \to y$ when the length-$(k-1)$ suffix of $x$ equals the prefix of $y$. A set $M$ of $k$-mers is a **decycling set** (an unavoidable set, or universal hitting set for all lengths) if $D_k \setminus M$ is acyclic; its **remaining path length** is the length of the longest path in the DAG $D_k \setminus M$. A context-free sketching method that selects $k$-mers by membership in a set $M$ has a **window guarantee** (every sufficiently long window of every sequence contributes a $k$-mer to the sketch) if and only if $M$ is a decycling set, and the guaranteed window size is governed by the remaining path length. Conversely, every sketching method with a window guarantee defines a decycling set.

**Minimum decycling sets.** The cycles of $D_k$ obtained by rotating a $k$-mer (pure cycling registers) partition the nodes, so every decycling set meets every rotation class. By the theorems of Mykkeltveit and Champarnaud, a **minimum decycling set** (MDS) contains exactly one $k$-mer per rotation class, and its size is the number of necklaces of length $k$.

**Companions and F-moves.** For $f \in \Sigma^{k-1}$ the left companions are $\mathrm{lc}(f) = \{af : a \in \Sigma\}$ and the right companions are $\mathrm{rc}(f) = \{fa : a \in \Sigma\}$; every left companion of $f$ has an edge to every right companion of $f$. An **F-move** at $f$ replaces the left companions by the right companions,

$$
fM = \big(M \cup \mathrm{rc}(f)\big) \setminus \mathrm{lc}(f), \qquad \text{valid when } \mathrm{lc}(f) \subseteq M ,
$$

and an RF-move is the reverse replacement.

**Proposition (existence).** Every MDS $M$ contains $\mathrm{lc}(f)$ for some $f \in \Sigma^{k-1}$ and $\mathrm{rc}(f')$ for some $f' \in \Sigma^{k-1}$.

**Proposition (F-moves preserve minimum decycling sets).** If $M$ is an MDS and $\mathrm{lc}(f) \subseteq M$, then $fM$ is an MDS.

**Lemma (commutativity).** If $f_1, f_2$ are both valid F-moves in an MDS $M$, then $f_1$ is valid in $f_2 M$, $f_2$ is valid in $f_1 M$, and $f_1 f_2 M = f_2 f_1 M$.

**Proposition (effect on the window).** An F-move or RF-move changes the remaining path length by at most $1$ in either direction. An I-move, which exchanges a mixed subset of left and right companions, can increase it by at most $1$ or decrease it by up to half.

## Expansion

For existence, suppose no right-companion set lies in $M$. Every $k$-mer $m$ is a left companion of its suffix $f_m$, and its out-neighbours are exactly $\mathrm{rc}(f_m)$, so some out-neighbour lies outside $M$. A walk avoiding $M$ can therefore be continued forever, and by finiteness it closes a cycle, contradicting decycling; the same argument on reversed edges gives a left-companion set. For preservation, the companions of $f$ form a complete bipartite block $K_{\sigma,\sigma}$. Any cycle through a right companion $fa$ enters it from some left companion, so with all of $\mathrm{lc}(f)$ removed no cycle passes through the block. Swapping in $\mathrm{rc}(f)$ blocks exactly the same cycles, and the swap keeps one $k$-mer per rotation class, because $af$ and $fa$ are rotations of each other. Sets reachable from the Mykkeltveit MDS by F-moves and I-moves form a graph on MDSs, and the paper conjectures that this graph is connected, so all MDSs can be enumerated by these local moves. Local search over the moves finds MDSs with short remaining path length, and computational evidence suggests that the Mykkeltveit set is already close to the minimum.

## Sources

- Guillaume Marçais, Dan DeBlasio and Carl Kingsford, "Sketching methods with small window guarantee using minimum decycling sets", arXiv (2023), Section 2 (window guarantee and decycling sets), Section 5 (Propositions 1 and 2, F-moves and I-moves, Conjectures 1 and 2), Section 6 (Proposition 3), appendix Lemma 1, <https://doi.org/10.48550/arXiv.2311.03592>.
- J. Mykkeltveit, "A proof of Golomb's conjecture for the de Bruijn graph", Journal of Combinatorial Theory, Series B 13 (1972), 40–45, <https://doi.org/10.1016/0095-8956(72)90006-8>.
