# Régin's filtering algorithm for ALLDIFFERENT

Given a matching that covers the variables of an ALLDIFFERENT constraint, all values without support are found in linear time by one search from the free values and one strongly connected components computation in an oriented value graph; with Hopcroft–Karp, GAC costs $O(m\sqrt p)$ in total for $p$ variables whose domains have total size $m$.

Let $G=(X,Y,E)$ be the [value graph](alldifferent-constraint.md) of $\mathrm{ALLDIFFERENT}(X)$ with $Y$ the union of the domains, $|X|=p$, $n=|X|+|Y|$ vertices and $m=|E|=\sum_i|D_i|$ edges, given by indexed vertices and adjacency lists (the domains listed explicitly), and let $M$ be a matching covering $X$. Orient $G$ into $G_o$: every edge of $M$ from its variable to its value, every edge of $E\setminus M$ from its value to its variable. The free vertices for $M$ all lie in $Y$.

**Theorem.**

1. An edge lies on a directed cycle of $G_o$ iff it lies on an even alternating cycle of $G$, and it lies on a directed simple path of $G_o$ starting at a free vertex iff it lies on an even alternating path of $G$ starting at a free vertex.
2. An edge $e$ belongs to no matching covering $X$ iff $e\notin M$, $e$ lies on no directed path of $G_o$ starting at a free vertex, and the two endpoints of $e$ are not [strongly connected](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/strongly-connected.md) in $G_o$.
3. Hence, given $M$, the set of such edges, which by the [matching criterion](alldifferent-gac-matching-criterion.md) are exactly the values to delete for GAC, is computed in $O(m+n)$ time by a breadth-first search from the free vertices and a linear-time strongly connected components algorithm. The edges of $M$ not marked in this way are the vital edges.
4. If some domain is empty the constraint fails at once. Otherwise $p\le m$ and $|Y|\le m$, and a matching covering $X$, or the information that none exists (failure), is found by the Hopcroft–Karp algorithm in $O(\sqrt p)$ phases of $O(m)$ time each, so in $O(m\sqrt p)$ time. Hence GAC on one ALLDIFFERENT constraint is enforced from scratch in $O(m\sqrt p)$ time and $O(m)$ space, which is $O(p^{1.5}d)$ when every domain has at most $d$ values.

5. Incrementally, along one branch of search on which values are only deleted, starting from a successful propagation with covering matching $M$: after deletions, the edges of $M$ that were deleted are re-covered by augmenting paths from the current matching (at most one augmenting-path search per lost matching edge, each $O(m)$) and item 3 is rerun. Régin bounds the total cost on one constraint along such a branch by $O(m^2)$ with $m$ the initial number of edges; since $m\le pd$, this is $O(p^2d^2)$.

## Depends on

- [The ALLDIFFERENT constraint and its value graph](alldifferent-constraint.md): value graph and covering matchings.
- [Strongly connected vertices](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/strongly-connected.md): the relation used in item 2.
- [Generalized arc consistency of ALLDIFFERENT by matchings](alldifferent-gac-matching-criterion.md): unsupported values are the edges in no covering matching.
- [Hopcroft–Karp](../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/maximum-bipartite-matching/hopcroft-karp.md): the matching algorithm named in item 4.
- [Edges lying in some maximum matching](../../../../GraphTheory/matchings-and-flows/edges-in-maximum-matchings/edges-in-some-maximum-matching.md): free vertices, even alternating paths and cycles, and vital edges, used in the statement; Berge's characterization is also applied to the covering matching $M$ in item 2.

## Proof depends on

- [Linear bound on the cost of BFS with parents](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/breadth-first-search/bfs-with-parents-time-le.md): the search from the free vertices in item 3, run from one added source joined to all free vertices.
- [Topological sort and Kosaraju SCC in O(n + m) word-RAM time](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/depth-first-search-applications-on-the-word-ram/linear-time-dfs-word-ram.md): its item (iv) computes the strongly connected components of $G_o$ in item 3.
- [Hopcroft-Karp in O((m + r + |E|) sqrt(nu)) word-RAM time](../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/flow-decompositions-separators-and-chain-covers/hopcroft-karp-word-ram.md): the maximum matching of item 4.

## Expansion

Item 1 (Régin's Proposition 1): parity is automatic for cycles because $G$ is bipartite. For paths, a directed simple path from a free vertex $y\in Y$ alternates free and matching edges; if it has odd length it ends at some $x\in X$, and since $x$ has its unique successor (its mate) not yet on the path (each value has at most one predecessor through $M$), the path extends by one matching edge to an even one.

Item 2: since $M$ covers $X$ it is a maximum matching, and covering matchings are exactly maximum matchings. By [Berge's characterization](../../../../GraphTheory/matchings-and-flows/edges-in-maximum-matchings/edges-in-some-maximum-matching.md), an edge outside $M$ lies in some maximum matching iff it lies on an even alternating path from a free vertex or on an even alternating cycle, i.e. by item 1 on a directed path from a free vertex or on a directed cycle of $G_o$; an edge lies on a directed cycle iff its endpoints are in the same strongly connected component.

Item 3: Régin's Algorithm 2 marks the edges reached by breadth-first search from the free vertices, computes the strongly connected components, marks the edges inside a component, and deletes the unmarked free edges. Régin uses Tarjan's algorithm for the components; any linear-time algorithm serves, and the linked word-RAM page gives one (Kosaraju's). The breadth-first search, from one added source with an arc to every free vertex, costs $O(n+m)$ by the linked BFS bound, and the components cost $O(n+m)$. The linked strongly-connected-components and Hopcroft–Karp pages count word-RAM instructions on graphs in compressed sparse row form with $n+m<2^w$, and building that form of $G_o$ (or of $G$) from the adjacency lists takes $O(n+m)$ instructions; the BFS bound counts dequeue attempts, adjacency checks, enqueues and parent writes, each a constant number of instructions. So the bounds of items 3 and 4 hold in that model.

Item 4: with every domain nonempty and $p\ge1$, each variable has an edge, so $m\ge p\ge1$, and every value lies in some domain, so $|Y|\le m$. The linked Hopcroft–Karp page computes a maximum matching of the value graph, with $p$ left vertices, $|Y|$ right vertices and $m$ edges, in $O((p+|Y|+m)\sqrt{\nu+1})$ instructions, $\nu\le p$ the maximum matching size; this is $O(3m\sqrt{2p})=O(m\sqrt p)$. If the matching has fewer than $p$ edges the constraint has no solution. With $p=0$ the constraint is trivially GAC. Régin states the initialisation cost as $O(d|X_C|\sqrt{|X_C|})$.

*Missing proof prerequisite (not expanded here).* A complete expansion adds a page for Régin's incremental bound, item 5: along a deletion-only branch, each lost matching edge is repaired by one augmenting-path search of cost $O(m)$, at most $m$ matching edges are lost in total, and each of the at most $m$ reruns of item 3 costs $O(m)$, so the total is $O(m^2)$; the page should state the incremental algorithm and prove this count, using the linked BFS bound for each augmenting-path search. Item 1 is proved above; item 2 follows from it with Berge's characterization of the edges in some maximum matching; item 3 rests on the linked BFS and strongly-connected-components running times; item 4 on the linked word-RAM Hopcroft–Karp bound.

## Sources

- J.-C. Régin, "A filtering algorithm for constraints of difference in CSPs", *Proceedings of the Twelfth National Conference on Artificial Intelligence (AAAI-94)*, AAAI Press (1994), 362–367, [https://aaai.org/papers/00362-AAAI94-055-a-filtering-algorithm-for-constraints-of-difference-in-csps/](https://aaai.org/papers/00362-AAAI94-055-a-filtering-algorithm-for-constraints-of-difference-in-csps/). Proposition 1 and its proof, Algorithm 2 (REMOVEEDGESFROMG) with its $O(m+n)$ analysis, Algorithm 3 (DIFF-PROPAGATION) and the $O(p^2d^2)$ bound, pp. 364–366.
- J. E. Hopcroft and R. M. Karp, "An $n^{5/2}$ algorithm for maximum matchings in bipartite graphs", *SIAM Journal on Computing* 2(4) (1973), 225–231, doi:10.1137/0202019. Theorem 3 (phase bound), used by Régin.
- R. Tarjan, "Depth-first search and linear graph algorithms", *SIAM Journal on Computing* 1(2) (1972), 146–160, doi:10.1137/0201010. Linear-time strongly connected components, used by Régin.
