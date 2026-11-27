# Deterministic (1 + eps)-approximate matching in poly(1/eps) semi-streaming passes

For every $0 < \varepsilon < 1$ there is a *deterministic* multi-pass streaming algorithm that, on an insertion-only edge stream (in adversarial order) of any $n$-vertex graph $G$, makes $\mathrm{poly}(1/\varepsilon)$ passes, uses $n \cdot \mathrm{poly}(1/\varepsilon) \cdot \log^{O(1)} n$ bits of memory and outputs a matching $M$ with

$$
|M| \ge \frac{\mu(G)}{1 + \varepsilon}.
$$

This improves exponentially on the $(1/\varepsilon)^{O(1/\varepsilon)}$ passes of McGregor's randomized algorithm, with no dependence of the pass count on $n$.

## Proof sketch

Start from a maximal matching computed in one pass. By the Hopcroft–Karp counting lemma, if $M$ is far from optimal then $G$ has many vertex-disjoint augmenting paths of length $O(1/\varepsilon)$ with respect to $M$. Each phase grows, in parallel from all free vertices, alternating structures of bounded size, extending or contracting them in each pass while keeping them vertex-disjoint; a charging argument shows that $\mathrm{poly}(1/\varepsilon)$ passes find a constant fraction of a maximal set of short disjoint augmenting paths, and $\mathrm{poly}(1/\varepsilon)$ phases reach a $(1 + \varepsilon)$-approximation.

## Depends on

- [Approximate maximum matching and vertex cover in a graph stream](approximate-matching-in-graph-streams.md)
- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](semi-streaming-graph-model.md)

## Proof depends on

- [Single-pass greedy maximal matching is a 1/2-approximate matching and 2-approximate vertex cover](single-pass-greedy-maximal-matching.md)
- [Augmenting path](../../../../GraphTheory/matchings-and-flows/berge-s-lemma/is-augmenting-walk.md)
- [A short augmenting path exists (Hopcroft–Karp, Corollary 2)](../../../../GraphTheory/matchings-and-flows/berge-s-lemma/exists-is-augmenting-walk-length-le.md)

## Sources

- Manuela Fischer, Slobodan Mitrović, Jara Uitto, "Deterministic (1+eps)-Approximate Maximum Matching with poly(1/eps) Passes in the Semi-Streaming Model and Beyond", STOC (2022), arXiv:2106.04179.
