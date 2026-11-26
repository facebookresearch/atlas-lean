# Maximal safe sequences as common leaves of dominator trees

**Setting.** $G=(V,E)$ is an $s$-$t$ graph with $m$ edges (cycles allowed): it has a unique source $s$ and a unique sink $t$, and every vertex is reachable from $s$ and can reach $t$ (this does not follow from uniqueness of the source and sink when cycles are present). It comes with its $s$- and $t$-dominator trees; $\mathrm{ext}(v)$ is the concatenation of the $s$-dominator-tree path from $s$ to $v$ and the $t$-dominator-tree path from $v$ to $t$; a sequence is safe for $C$-walk covers iff it is a subsequence of $\mathrm{ext}(v)$ for some $v\in C$.

**Univocal paths and collapsing.** A path $v_1\dots v_k$ ($k\ge1$) is *univocal* if in the $t$-dominator tree each $v_{i+1}$ has $v_i$ as its unique child and in the $s$-dominator tree each $v_i$ has $v_{i+1}$ as its unique child. Distinct maximal univocal paths are vertex-disjoint. Collapsing each maximal univocal path to one vertex (which stores the collapsed sequence) preserves all extensions, hence all maximal safe sequences. For $C\subseteq V$ the same is done on the *$C$-dominator trees* obtained by keeping only vertices appearing in extensions of vertices of $C$, with univocality defined through unique children in $C$.

**Theorem.** Let $G$ be such an $s$-$t$ graph, so both dominator trees span $V$, and let $C\subseteq V$.

1. If the dominator trees are collapsed (with respect to $C$), then for $u\in C$, $\mathrm{ext}(u)$ is a maximal $C$-safe sequence if and only if $u$ is a leaf in both dominator trees.
2. There is an $O(m+o)$-time algorithm that outputs all maximal $C$-safe sequences without duplicates, where $o$ is their total length; the collapsed trees represent all of them in $O(|V|)$ space.

## Depends on

- [Dominator characterization of safe sequences for walk covers](dominator-characterization-of-safe-sequences-for-walk-covers.md)

## Expansion

If $u$ has a child $w$ in the $s$-dominator tree, then $\mathrm{ext}(w)$ passes through $u$ and, by the interaction lemma between $s$- and $t$-dominators, contains $\mathrm{ext}(u)$ as a proper subsequence unless $u$ and $w$ lie on a common univocal path; symmetrically for children in the $t$-dominator tree. After collapsing univocal paths, every non-leaf in either tree is therefore dominated by a longer extension, while extensions of common leaves are pairwise incomparable. Dominator trees of a directed graph are computable in linear time, collapsing is a linear scan, and each maximal sequence is printed by walking two tree paths, giving $O(m+o)$. This generalizes the earlier DAG case, where graph compression plays the role of collapsing, to graphs with cycles.

## Sources

- F. Sena, A. I. Tomescu, "Fast and flexible flow decompositions in general graphs via dominators", arXiv:2511.19153 (2025), <https://doi.org/10.48550/arXiv.2511.19153>. Section 3 (Definition 2, Lemma 2, Theorems 2, 3, 5 and 6).
