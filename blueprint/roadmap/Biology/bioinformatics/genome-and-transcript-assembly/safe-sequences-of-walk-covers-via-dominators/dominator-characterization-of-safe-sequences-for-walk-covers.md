# Dominator characterization of safe sequences for walk covers

**Setting.** An $s$-$t$ graph $G=(V,E)$ is a directed graph without parallel edges (self-loops allowed) with a unique source $s$ and unique sink $t$, in which every vertex is reachable from $s$ and can reach $t$; it may contain cycles. (The reachability requirement is part of the hypothesis: a unique source and sink do not imply it in a cyclic graph. With edges $s\to t$, $s\to u$, $u\to v$, $v\to u$, the only source is $s$ and the only sink is $t$, yet no $s$-$t$ walk visits $u$. For an arbitrary digraph with distinguished $s,t$, one first restricts to the subgraph of vertices reachable from $s$ and co-reachable to $t$; a set $C$ meeting a vertex outside it admits no $C$-walk cover, and the notion of $C$-safety is not used for such $C$.) A walk may repeat vertices and edges. For $C\subseteq V$, a *$C$-walk cover* is a set of $s$-$t$ walks such that every vertex of $C$ lies on some walk. A sequence $X=u_1,\dots,u_\ell$ of vertices (with a $u_i$-$u_{i+1}$ path for each $i$) is *$C$-safe* if every $C$-walk cover contains a walk having $X$ as a subsequence.

**Dominators.** $u$ *$s$-dominates* $v$ if every $s$-$v$ path contains $u$, and $u$ *$t$-dominates* $v$ if every $v$-$t$ path contains $u$. Because every vertex lies on an $s$-$t$ walk, $s$ $s$-dominates and $t$ $t$-dominates every vertex, so these relations are represented by the $s$-dominator tree (rooted at $s$, parent = immediate $s$-dominator) and the $t$-dominator tree. For $v\in V$, the *extension* $\mathrm{ext}(v)$ is the sequence obtained by concatenating the tree path from $s$ to $v$ in the $s$-dominator tree with the tree path from $v$ to $t$ in the $t$-dominator tree.

**Theorem.** Let $G$ be an $s$-$t$ graph (so every vertex is reachable from $s$ and reaches $t$) and $C\subseteq V$. A sequence $X$ of vertices is $C$-safe if and only if there is a vertex $v\in C$ such that $X$ is a subsequence of $\mathrm{ext}(v)$. (For $C=V$: $X$ is safe for walk covers iff it is a subsequence of some $\mathrm{ext}(v)$.)

**Lemma.** If $u$ is the $k$-th ancestor of $v$ in the $s$-dominator tree, then the $k$-th ancestor $dom_t(u,k)$ of $u$ in the $t$-dominator tree $t$-dominates $v$, and $v$ is not a $t$-dominator of $u$ unless $v=dom_t(u,k)$.

Edge sequences and edge subsets $C\subseteq E$ reduce to the vertex case by subdividing each edge of $C$ with a new vertex.

## Expansion

Reachability guarantees that a $C$-walk cover exists for every $C\subseteq V$ and that both dominator trees span $V$. Sufficiency: any walk through $v\in C$ must, by definition of domination, visit all $s$-dominators of $v$ in their tree order before $v$ and all $t$-dominators of $v$ in order after it, so it contains $\mathrm{ext}(v)$ as a subsequence, and every $C$-walk cover has such a walk. Necessity: if $X$ is not a subsequence of any $\mathrm{ext}(v)$ with $v\in C$, then for each $v\in C$ one can route an $s$-$t$ walk through $v$ that avoids completing $X$, using an $s$-$v$ path missing some element of $X$ that is not an $s$-dominator of $v$, or a $v$-$t$ path doing the same; these walks form a cover with no walk containing $X$. The lemma describes how the two dominance relations interact along ancestor chains and is the main tool for the maximality characterization.

## Sources

- F. Sena, A. I. Tomescu, "Fast and flexible flow decompositions in general graphs via dominators", arXiv:2511.19153 (2025), <https://doi.org/10.48550/arXiv.2511.19153>. Section 2 (definitions of $s$-$t$ graphs, walk covers, safety, dominators and extensions) and Section 3 (Theorems 1 and 4, Lemma 1).
