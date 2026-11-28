# Exact quartet-maximizing level-1 extension of a constraint tree

**Setting.** A rooted binary phylogenetic network is **level-1** if its cycles (in the underlying undirected graph) are pairwise vertex-disjoint; each cycle has a unique reticulation node of in-degree $2$. Deleting one incoming edge at every reticulation, in every possible way, yields the set $\mathcal{T}(N)$ of displayed trees, and $N$ is obtained from any $t \in \mathcal{T}(N)$ by adding non-tree edges. Let $Q(N)$ be the set of unrooted resolved quartet trees displayed by trees in $\mathcal{T}(N)$.

Fix a rooted binary tree $T$ on $n$ taxa (the constraint tree) and a multiset $\mathcal{Q}$ of quartet trees. *Adding an edge above $(u,w)$* for nodes $u, w$ of $T$ subdivides the edges above $u$ and $w$ by new nodes $u', w'$ and inserts the arc $(u', w')$; this creates one cycle $\gamma(u,w)$ whose reticulation is $w'$, and $v = \mathrm{lca}_T(u,w)$ is called the **target** of the new edge. A quartet $q$ is **satisfied** by an extension $N$ of $T$ if $q \in Q(N) \setminus Q(T)$, and by a single edge $e$ if it is satisfied by $T + e$ (all other non-tree edges removed).

**Problem.** Find a level-1 network $N$ extending $T$ maximizing the number of quartets of $\mathcal{Q}$ (with multiplicity) satisfied by $N$.

**Lemma 1 (unique credit).** If $N$ extends $T$ and is level-1, every quartet satisfied by $N$ is satisfied by $T + e$ for exactly one non-tree edge $e$; the satisfied set is the disjoint union over non-tree edges.

**Lemma 2 (one edge per target).** In a level-1 extension of $T$, each node $v$ of $T$ is the target of at most one non-tree edge.

**Dynamic program.** Let $s_e(u,w)$ be the number of quartets of $\mathcal{Q}$ satisfied by an edge added above $(u,w)$, and $M[v]$ the best score using only edges with targets in the subtree $T_v$. With $M[v] = 0$ at leaves,

$$M[v] = \max\Bigl\{ M[l(v)] + M[r(v)],\ \max_{(u,w) \in \mathrm{Pairs}(v)} \bigl( s_e(u,w) + s_{dp}(v,u,w) \bigr) \Bigr\},$$

where $\mathrm{Pairs}(v)$ are the ordered pairs with $\mathrm{lca}_T(u,w) = v$ (including $u = v$ with $w$ below $v$, which models a ghost lineage, except at the root) and, for $u \neq v$,

$$s_{dp}(v,u,w) = M[u] + M[w] + \sum_{x \in \gamma(u,w) \cap V(T) \setminus \{v\}} \begin{cases} M[l(x)] & \text{if } l(x) \in \gamma(u,w), \\ M[r(x)] & \text{otherwise,}\end{cases}$$

which collects the best scores of the subtrees hanging off the cycle (for $u = v$ drop the $M[u]$ term and sum over all tree nodes of the cycle).

**Theorem 1.** $M[r]$ at the root $r$ of $T$ is the maximum number of quartets of $\mathcal{Q}$ satisfiable by a level-1 extension of $T$, and backtracking returns an optimal network. It runs in $O(n^2(|\mathcal{Q}| + n))$ time and $O(n^4)$ space, where $|\mathcal{Q}|$ counts distinct quartet topologies. Indexing the table also by the number $k \le m \le n-1$ of added edges returns, for every $k$, an optimal level-1 extension with exactly $k$ reticulations in $O(n^2(|\mathcal{Q}| + m^3 n))$ time.

## Expansion

Correctness is by strong induction on subtree size. In an optimal extension of $T_y$, either no edge targets $y$ (score $M[l(y)] + M[r(y)]$), or exactly one does (Lemma 2), say above $(a,b)$. Its own contribution $s_e(a,b)$ is independent of other edges by Lemma 1. Every other cycle must avoid $\gamma(a,b)$, so its target lies strictly inside a subtree hanging off the cycle, and those subtrees are optimized independently, which is what $s_{dp}$ sums. After $O(n^2)$ preprocessing for constant-time LCA queries, $\delta_T(q,(u,w))$ is decided in $O(1)$ from where the four leaves attach to the cycle; each candidate edge is examined in only one $s(\cdot)$, giving the stated bound.

The score never decreases with more reticulations, so the per-$k$ table is used to choose the number of reticulations where the improvement levels off. With an exact quartet-based species-tree method supplying $T$ and an outgroup rooting it, the two-stage pipeline is statistically consistent for the network whenever the most probable quartet on every four taxa is induced by one tree displayed by the true network and the quartet input converges to that network's quartet set.

## Sources

- J. Willson, T. Warnow, "CAMUS: scalable phylogenetic network estimation", Bioinformatics (2026) btag245, Definitions 1–5, Lemmas 1–2, Equations (1)–(5), Theorem 1 and Sections 2.3–2.4, <https://doi.org/10.1093/bioinformatics/btag245>, PMCID PMC13340232.
