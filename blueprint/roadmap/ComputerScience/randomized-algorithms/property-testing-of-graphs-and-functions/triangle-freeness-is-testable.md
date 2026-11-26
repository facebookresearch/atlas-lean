# Triangle-freeness is testable with a constant number of queries

The triangle tester samples $k$ independent uniformly random ordered vertex triples and rejects iff some sampled triple spans a triangle. On a graph with $t$ triangles one trial accepts with probability exactly $1 - 6t/n^3$. By the triangle removal lemma, for every $\varepsilon > 0$ there is $\delta(\varepsilon) > 0$ such that every graph $\varepsilon$-far from triangle-free has at least $\delta(\varepsilon) n^3$ triangles (Goldreich 2017, Theorem 8.18, Part 1); hence $k = O(1/\delta(\varepsilon))$ trials give a one-sided tester whose query complexity depends only on $\varepsilon$.

## Proof sketch

Each triangle is hit by $6$ of the $n^3$ ordered triples. The removal lemma, proved from Szemerédi's regularity lemma, converts farness from triangle-freeness into many triangles; independent repetition amplifies the per-trial rejection probability $6\delta$.

## Depends on

- [Property testing in the dense graph model](dense-graph-property-testing-model.md)

## Sources

- N. Alon, R. A. Duke, H. Lefmann, V. Rödl and R. Yuster, "The Algorithmic Aspects of the Regularity Lemma", Journal of Algorithms 16(1), 1994.
- N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, "Efficient Testing of Large Graphs", Combinatorica 20(4), 2000.
- O. Goldreich, "Introduction to Property Testing", Cambridge University Press, 2017.
