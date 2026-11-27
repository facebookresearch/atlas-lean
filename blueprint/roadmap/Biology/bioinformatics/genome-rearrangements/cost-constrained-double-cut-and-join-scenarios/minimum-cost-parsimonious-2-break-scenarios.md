# Minimum-cost parsimonious 2-break scenarios

**Setting.** A *graph* here is an Eulerian 2-edge-coloured undirected multigraph $G = (V, E^b \cup E^g)$ with black and gray edges, $e(G) = |E^b| = |E^g|$; breakpoint graphs of two genomes (including genomes with unequal gene content, under the usual Double Cut and Join variants) are instances. A **2-break** replaces two black edges $(x_1,x_2),(x_3,x_4)$ by $(x_1,x_3),(x_2,x_4)$ or $(x_1,x_4),(x_2,x_3)$; a *scenario* is a sequence of 2-breaks after which every black edge is parallel to a gray edge. Let $c(G)$ be the maximum number of cycles in a decomposition of $G$ into edge-disjoint alternating cycles (MACD).

**Theorem.**

*(1)* (Parsimonious length) The minimum length of a 2-break scenario is $l(G) = e(G) - c(G)$, and the cycles traced by any parsimonious scenario form a maximum alternating cycle decomposition.

*(2)* (Decomposition) For any cost function $\varphi$ on 2-breaks, the minimum cost of a parsimonious scenario equals

$$\min_{C\ \text{a MACD of}\ G}\ \sum_{c\in C}\mathrm{MCPS}_\varphi(c),$$

and the cost of a simple cycle is the minimum cost over its Eulerian circles. So the problem reduces to independent instances on *circles* (graphs where each vertex meets exactly one black and one gray edge).

*(3)* (Coloured cost) Colour the vertices and let a 2-break cost $0$ if it preserves the multiset of colour pairs of the two edges and $1$ otherwise (e.g. $(x,y),(z,t) \to (x,z),(y,t)$ is free iff $\mathrm{col}(x) = \mathrm{col}(t)$ or $\mathrm{col}(y) = \mathrm{col}(z)$), modelling spatial proximity of loci in the nucleus. Let $J(G,\mathrm{col})$ be the graph obtained by merging same-coloured vertices. For two genomes $A$ and $B$ with breakpoint graph $G(A,B)$ and $J=J(G(A,B),\mathrm{col})$, the minimum cost over all (not necessarily parsimonious) DCJ scenarios transforming $A$ into $B$ is $e(J)-c(J)$. Deciding for a circle $O$ and a bound $k$ whether $O$ has a scenario of cost at most $k$ is NP-hard.

*(4)* (Parsimonious coloured cost) For two genomes with $n$ genes, a minimum-cost parsimonious DCJ scenario for the coloured cost is computable in $O(n^4)$ time.

## Expansion

Each 2-break changes the number of cycles in a best decomposition by at most one, which gives the lower bound $e - c$; splitting one cycle at a time attains it, and conversely a parsimonious scenario must split along a maximum decomposition. Because 2-breaks inside different cycles never interact in a parsimonious scenario, costs add over the cycles. Under the coloured cost, free moves are exactly those invisible in the colour-merged graph, so cost equals length in $J$; computing $c(\cdot)$ of a general Eulerian graph is hard, which is the source of NP-hardness without parsimony.

## Sources

- Pijus Simonaitis, Annie Chateau and Krister M. Swenson, "A framework for cost-constrained genome rearrangement under Double Cut and Join", Algorithms Mol. Biol. 14:15 (2019), items (1), (2) and the NP-hardness in (3); preprint arXiv:1802.07515 (2018), Section 2 (Theorem 1, Corollary 1), Section 3 (Theorems 2 and 3) and Section 4 (Theorem 5), <https://doi.org/10.48550/arXiv.1802.07515>.
- Pijus Simonaitis and Krister M. Swenson, "Finding local genome rearrangements", Algorithms Mol. Biol. 13:9 (2018), Theorem 2 (minimum coloured cost $e(J)-c(J)$ for two genomes).
- Krister M. Swenson, Pijus Simonaitis and Mathieu Blanchette, "Models and algorithms for genome rearrangement with positional constraints", Algorithms Mol. Biol. 11:13 (2016) ($O(n^4)$ algorithm for item (4)), <https://doi.org/10.1186/s13015-016-0065-9>.
