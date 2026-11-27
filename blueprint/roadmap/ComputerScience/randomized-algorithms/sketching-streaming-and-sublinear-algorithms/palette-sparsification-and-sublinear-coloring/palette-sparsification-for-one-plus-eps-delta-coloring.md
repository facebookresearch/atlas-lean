# Palette sparsification for (1 + eps)Delta-coloring needs only Theta(sqrt(log n)) samples

For every $\varepsilon \in (0, 1)$ there are constants $C_\varepsilon, c_\varepsilon > 0$ such that:

1. for every $n$-vertex graph of maximum degree $\Delta$, if every vertex independently samples $\lceil C_\varepsilon\sqrt{\log n}\,\rceil$ colors uniformly from $\{1, \dots, \lceil (1 + \varepsilon)\Delta\rceil\}$, then with high probability the graph has a proper coloring from the sampled lists;
2. there are $n$-vertex graphs of maximum degree $\Delta$ on which sampling at most $c_\varepsilon\sqrt{\log n}$ colors per vertex from $\{1, \dots, \lceil (1 + \varepsilon)\Delta\rceil\}$ leaves no proper coloring from the samples with probability bounded away from zero.

So the extra $\varepsilon\Delta$ colors reduce the required sample size from $\Theta(\log n)$ to $\Theta(\sqrt{\log n})$.

## Proof sketch

With $\varepsilon\Delta$ spare colors, sparse vertices have slack from the start, and almost-cliques have palettes larger than their size by a constant factor. A saturating matching in a random palette graph with this surplus exists once each vertex samples about $\sqrt{\log n}$ colors, since Hall violations now require a set $S$ and a target set of size noticeably smaller than $|S|$, and the probability of each violation decays like $\exp(-\Omega(s^2))$ in the sample size $s$. For the lower bound, a disjoint union of many cliques is used: each clique independently fails to be colorable from its samples with probability roughly $\exp(-O(s^2))$, so with $n/\Delta$ cliques some clique fails once $s$ is a small multiple of $\sqrt{\log n}$.

## Depends on

- [Palette sparsification experiment, sampled lists and the conflict graph](palette-sparsification-experiment.md)

## Proof depends on

- [Assadi-Chen-Khanna palette sparsification theorem for (Delta + 1)-coloring](palette-sparsification-theorem-delta-plus-one.md)
- [Almost-cliques are list-colorable from random samples via saturating matchings of the palette graph](almost-cliques-colored-via-palette-graph-matchings.md)

## Sources

- Noga Alon, Sepehr Assadi, "Palette Sparsification Beyond (Delta+1) Vertex Coloring", APPROX/RANDOM (2020), arXiv:2006.10456.
