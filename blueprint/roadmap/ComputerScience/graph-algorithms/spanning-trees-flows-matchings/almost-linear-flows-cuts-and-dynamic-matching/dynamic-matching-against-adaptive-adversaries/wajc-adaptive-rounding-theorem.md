# Wajc: dynamic rounding of fractional matchings against adaptive adversaries

Combining dynamic fractional matching algorithms with randomized kernel rounding yields the following algorithms, all of whose guarantees hold against an adaptive adversary:

1. for every $\varepsilon \in (0, 1/2)$, a Las Vegas randomized $(2 + \varepsilon)$-approximate dynamic matching algorithm with $\mathrm{poly}(\log n, 1/\varepsilon)$ worst-case update time with high probability;
2. for every $\varepsilon \in (0, 1/2)$, a randomized $(2 + \varepsilon)$-approximate algorithm with $\mathrm{poly}(1/\varepsilon)$ amortized update time, where approximation and time hold in expectation;
3. for every constant $\varepsilon > 0$ there is a constant $\delta > 0$ and a randomized $(2 - \delta)$-approximate dynamic matching algorithm for bipartite graphs with expected update time $O(n^{\varepsilon})$.

Previously all randomized algorithms with these trade-offs required an oblivious adversary.

## Proof sketch

Maintain a fractional matching $x$ deterministically, so its evolution does not depend on random bits, and sample a kernel $H$ from the colour classes of $x$. The sampled $H$ has $\tilde O(\mu(G))$ edges; when $x$ is approximately maximal, negative association shows that $H$ contains a randomized kernel, so $\mathbb{E}[\mu(H)] \ge \mu(G)/(2 + O(\varepsilon))$ by the kernel lemma (for item 3, a bipartite fractional matching algorithm with better-than-2 approximation is rounded the same way). Resampling after a geometric number of updates and recomputing a near-maximum matching in $H$ costs little amortized or, with periodic background rebuilding, worst-case time, and since fresh randomness is used each time, the adversary learns nothing that biases future samples.

## Depends on

- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)
- [Fully dynamic alpha-approximate maximum matching and its value version](dynamic-approximate-matching-problem.md)

## Proof depends on

- [The augmenting-path maximum matching](../../maximum-bipartite-matching/max-matching.md)
- [Sampling colour classes of edge-coloured fractional matchings with negative association](colour-class-sampling-lemma.md)
- [Deterministic (c, d, 0)-kernels preserve maximum matching within 2c(1+1/d)](kernel-approximation-lemma.md)

## Sources

- David Wajc, "Rounding Dynamic Matchings Against an Adaptive Adversary", STOC (2020), arXiv:1911.05545.
- Sayan Bhattacharya, Monika Henzinger, Giuseppe F. Italiano, "Deterministic Fully Dynamic Data Structures for Vertex Cover and Matching", SODA (2015), arXiv:1412.1318.
