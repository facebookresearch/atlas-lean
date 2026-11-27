# Palette sparsification for (1 + eps)Delta-coloring needs only Theta(sqrt(log n)) samples

1. For every $\varepsilon \in (0, 1/2)$ there is an integer $n_0(\varepsilon)$ such that for every graph with $n \ge n_0(\varepsilon)$ vertices and maximum degree $\Delta$, if every vertex independently samples a uniformly random set of $O\big(\sqrt{\log n}/\varepsilon^{1.5}\big)$ colors from $\{1, \dots, (1 + \varepsilon)\Delta\}$, then with high probability the graph has a proper coloring from the sampled lists.
2. The order $\sqrt{\log n}$ cannot be lowered: there is an $n$-vertex graph of maximum degree $\Delta = 0.5\sqrt{\log n}$ such that if every vertex independently samples $\ell = 0.5\sqrt{\log n}$ colors uniformly from $\{1, \dots, 2\Delta\}$, then with probability $1 - o(1)$ there is no proper coloring from the sampled lists.

So the extra $\varepsilon\Delta$ colors reduce the required sample size from $\Theta(\log n)$, which is necessary for $(\Delta + 1)$-coloring, to $\Theta(\sqrt{\log n})$.

## Proof sketch

For part 1, view the sampled lists as a list-coloring instance and use the c-degree of a vertex-color pair $(v, c)$, the number of neighbors of $v$ whose lists also contain $c$. Reed and Sudakov proved that a graph is colorable from lists whose sizes exceed the maximum c-degree by a factor $1 + o(1)$. The sampled lists of size $\Theta(\sqrt{\log n})$ do not concentrate well enough to satisfy this condition directly, so it is applied to carefully chosen sublists of the samples. For part 2, take a disjoint union of $n/(\ell + 1)$ cliques on $\ell + 1$ vertices. A clique cannot be colored when all of its lists lie inside $\{1, \dots, \ell\}$, which happens with probability $\binom{2\ell}{\ell}^{-(\ell + 1)} \ge 2^{-2\ell^2} = n^{-1/2}$, independently across the $\omega(n^{1/2})$ cliques.

## Depends on

- [Palette sparsification experiment, sampled lists and the conflict graph](palette-sparsification-experiment.md)

## Sources

- Noga Alon, Sepehr Assadi, "Palette Sparsification Beyond (Delta+1) Vertex Coloring", APPROX/RANDOM (2020), arXiv:2006.10456.
