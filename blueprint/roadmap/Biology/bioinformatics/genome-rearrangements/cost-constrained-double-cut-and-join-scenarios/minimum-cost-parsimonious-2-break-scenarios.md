# Minimum-cost parsimonious 2-break scenarios

**Setting.** A *graph* here is an Eulerian 2-edge-coloured undirected multigraph $G = (V, E^b \cup E^g)$ with black and gray edges, $e(G) = |E^b| = |E^g|$; breakpoint graphs of two genomes (including genomes with unequal gene content, under the usual Double Cut and Join variants) are instances. A **2-break** replaces two black edges $(x_1,x_2),(x_3,x_4)$ by $(x_1,x_3),(x_2,x_4)$ or $(x_1,x_4),(x_2,x_3)$; a *scenario* is a sequence of 2-breaks after which every black edge is parallel to a gray edge. Let $c(G)$ be the maximum number of cycles in a decomposition of $G$ into edge-disjoint alternating cycles (MACD).

**Theorem.**

*(1)* (Parsimonious length) The minimum length of a 2-break scenario is $l(G) = e(G) - c(G)$, and the cycles traced by any parsimonious scenario form a maximum alternating cycle decomposition.

*(2)* (Decomposition) For any non-negative cost function $\varphi$ on 2-breaks, the minimum cost of a parsimonious scenario equals

$$\min_{C\ \text{a MACD of}\ G}\ \sum_{c\in C}\mathrm{MCPS}_\varphi(c),$$

and the cost of a simple cycle is the minimum cost over its Eulerian circles. So the problem reduces to independent instances on *circles* (graphs where each vertex meets exactly one black and one gray edge).

## Expansion

Each 2-break changes the number of cycles in a best decomposition by at most one, which gives the lower bound $e - c$; splitting one cycle at a time attains it, and conversely a parsimonious scenario must split along a maximum decomposition. Because 2-breaks inside different cycles never interact in a parsimonious scenario, costs add over the cycles. (Vertex-coloured cost results from the preprint arXiv:1802.07515 §§4–5, which do not appear in the published AMB 14:15 edge-colour framework, are held out of this statement.)

## Sources

- Pijus Simonaitis, Annie Chateau and Krister M. Swenson, "A framework for cost-constrained genome rearrangement under Double Cut and Join", *Algorithms for Molecular Biology* 14:15 (2019), Lemma 1, Lemma 3, Theorems 1–2 (<https://doi.org/10.1186/s13015-019-0150-y>; preprint arXiv:1802.07515, Sections 2–3).
