# Edges lying in some maximum matching

Given one maximum matching $M$ of a graph, an edge lies in some but not every maximum matching exactly when it lies on an even alternating path that starts at a vertex left free by $M$, or on an even alternating cycle (Berge).

Let $G$ be a finite graph and $M$ a matching of $G$, that is, a set of edges of $G$ no two distinct members of which share a vertex; $M$ is maximum when no matching of $G$ has more edges. An edge of $M$ is a *matching edge*, every other edge is *free*; a vertex is *matched* if it is incident to a matching edge and *free* otherwise. An **alternating path** (resp. **cycle**) is a simple path (resp. cycle) whose edges are alternately matching and free; its length is its number of edges, and it is *even* when that number is even.

**Theorem.** Let $M$ be a maximum matching of $G$ and $e$ an edge of $G$. Then $e$ belongs to some but not to every maximum matching of $G$ if and only if $e$ lies on an even alternating path (with respect to $M$) that begins at a free vertex, or on an even alternating cycle.

Consequently, the edges belonging to at least one maximum matching are the edges of $M$ together with the edges of all even alternating paths starting at a free vertex and of all even alternating cycles; an edge in every maximum matching is called *vital*.

## Depends on

None.

## Proof depends on

- [Berge's lemma](../berge-s-lemma/berge.md): a maximum matching admits no augmenting path, so the symmetric difference of two maximum matchings has no odd alternating path component.

## Expansion

($\Leftarrow$) Let $P$ be an even alternating path from a free vertex, or an even alternating cycle. Exchanging the matching and free edges of $P$ gives a matching $M\oplus E(P)$ with $|M|$ edges: on a cycle the two edge classes have equal size, and on an even path from a free vertex $u$ the first edge is free (since $u$ is free), the last edge is a matching edge, and the far endpoint becomes free. So $M\oplus E(P)$ is maximum, and exactly one of $M$ and $M\oplus E(P)$ contains $e$.

($\Rightarrow$) Suppose maximum matchings $M_1\ni e$ and $M_2\not\ni e$ exist. If $e\in M$, take $M'=M_2$, otherwise $M'=M_1$; then $e\in M\oplus M'$. Every vertex has degree at most 2 in $M\oplus M'$, so its components are alternating paths and even alternating cycles. A path component of odd length would have both end edges in the same matching and would be augmenting for the other one, contradicting maximality by Berge's lemma; so the component $P$ containing $e$ is an even cycle or an even path. An even path component has one end edge in $M$ and one in $M'$; its endpoint whose edge is in $M'$ is free for $M$ (otherwise the path would continue), so $P$ is an even alternating path beginning at an $M$-free vertex.

Régin quotes the theorem from Berge's *Graphes et hypergraphes* (1970) without proof and uses it in bipartite value graphs to find all edges belonging to no matching that covers the variables.

## Sources

- J.-C. Régin, "A filtering algorithm for constraints of difference in CSPs", *Proceedings of the Twelfth National Conference on Artificial Intelligence (AAAI-94)*, AAAI Press (1994), 362–367, [https://aaai.org/papers/00362-AAAI94-055-a-filtering-algorithm-for-constraints-of-difference-in-csps/](https://aaai.org/papers/00362-AAAI94-055-a-filtering-algorithm-for-constraints-of-difference-in-csps/). Definition 6 and Property 1 (attributed to Berge 1970), p. 364.
