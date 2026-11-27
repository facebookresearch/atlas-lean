# Fixation bounds for bipartite and lattice dispersal graphs

Consider the neutral [Moran process on two dispersal graphs](moran-process-on-two-dispersal-graphs.md).

**Two islands.** For even $N$, let $B_N = K_{N/2,N/2}$ be the complete bipartite graph (offspring always cross to the other island) and $T_N$ the two-clique graph (two disjoint copies of $K_{N/2}$ joined by a perfect matching, so offspring rarely cross). Both have $N^2/4$ edges and are $N/2$-regular. Then, for residents on $K_N$,

$$\rho(B_N, K_N) > \frac{1}{e-1}\cdot\frac1N, \qquad \rho(K_N, B_N) < \frac{e}{e-1}\cdot\frac1N,$$

so losing about half of the edges in the bipartite way costs only a constant factor; numerically $N\rho(B_N, K_N) \approx 0.82$, whereas $N\rho(T_N, K_N) \to 0$. Two structures with equal edge count and degree can thus behave very differently.

**One-dimensional lattices.** Let $\mathrm{Cir}^d_N$ be the cycle on $N$ sites with each site joined to its $d/2$ nearest sites on each side, and $\rho^{1D}_N(d_1, d_2) = \rho(\mathrm{Cir}^{d_1}_N, \mathrm{Cir}^{d_2}_N)$. Then

$$0.138 \;<\; \lim_{N\to\infty}\rho^{1D}_N(4, 2) \;<\; 0.34 .$$

A neutral mutant that disperses to its two nearest neighbours on each side therefore fixes with probability bounded away from $0$ in arbitrarily large rings of nearest-neighbour residents, exactly as an advantageous mutant does in a well-mixed population. Simulations show the converse dichotomy: when $d_1 < d_2$ the fixation probability decays exponentially in $N$, and the same holds on two-dimensional periodic lattices. The *effective fitness* $r$ defined by $\rho(L_N, L'_N) = (1 - r^{-1})/(1 - r^{-N})$ is then roughly independent of $N$ (about $1.06$ for 8-neighbour versus 4-neighbour square lattices).

## Depends on

- [Moran process on two dispersal graphs](moran-process-on-two-dispersal-graphs.md)
- [Fixation probability of the Moran process](../../../../population-genetics/moran-model/moran-fixation.md)

## Proof sketch

On $B_N$ with $n$ mutants split $k$ and $n-k$ between the islands, the probability of gaining a mutant in one step is $p_+(k, n-k) = n/N - 4k(n-k)/N^2$; the mutant numbers on the two sides stay balanced because surplus mutants on one side seed the other, and comparing with a biased walk gives the $1/(e-1)$ factor (Theorem B.1). On $T_N$, a mutant lineage stays trapped in one clique where mutants block each other twice as often, which drives $N\rho(T_N, K_N)$ to $0$. For the rings, the upper bound follows from the first active step out of a single mutant (two extinction moves of weight $\frac1N\cdot\frac12$ against four growth moves of weight $\frac1N\cdot\frac14$); the lower bound comes from a stochastic-domination argument showing that a long contiguous mutant block expands more often than it shrinks, because degree-4 mutants can skip over a boundary resident and later fill the gap (Theorem C.1).

## Sources

- J. Tkadlec, K. Kaveh, K. Chatterjee, M. A. Nowak, "Evolutionary dynamics of mutants that modify population structure", Journal of the Royal Society Interface (2023), <https://doi.org/10.1098/rsif.2023.0355> (PMC10684346).
