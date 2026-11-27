# Moran process on two dispersal graphs

Let $G_A$ and $G_B$ be two connected undirected graphs on the same $N$ sites, each site holding one individual of type $A$ (mutant) or $B$ (resident), with reproductive rates $r_A$ and $r_B$. Their dispersal matrices are $m^X_{ij} = 1/\deg_{G_X}(i)$ if $i$ and $j$ are adjacent in $G_X$ and $0$ otherwise, for $X \in \{A, B\}$. In each step one individual is chosen to reproduce with probability proportional to its rate; if it has type $X$ and sits at $i$, its offspring replaces the individual at $j$ with probability $m^X_{ij}$. Mutant offspring therefore move along $G_A$ and resident offspring along $G_B$. The process is a Markov chain on $\{0,1\}^N$ with absorbing states all-$A$ and all-$B$.

Let $\rho(G_A, G_B)$ be the probability that a single mutant at a uniformly random site takes over, in the neutral case $r_A = r_B$. Then:

- if $G_A = G_B$, $\rho(G_A, G_B) = 1/N$ for every connected graph;
- if $G_A \ne G_B$, $\rho(G_A, G_B)$ can be above or below $1/N$, even when $G_A$ and $G_B$ are isomorphic but not identical (for two differently labelled 4-vertex Stars the value is $63/208 \approx 0.303 > 1/4$).

A mutant that disperses on more edges than the resident tends to have $\rho > 1/N$, but this is not monotone: adding edges to $G_A$ can lower $\rho(G_A, K_N)$ (on 6 sites, a cycle with a pendant vertex beats the graph obtained by joining its degree-3 vertex to all others), and among regular graphs with the same degree $\rho(\cdot, K_N)$ can differ, so the isothermal theorem does not extend to two graphs.

## Proof depends on

- [Absorption probabilities and mean times of a finite Markov chain](../../../../../Probability/markov-chains/finite-markov-chains/absorption-probabilities-and-mean-absorption-tim.md)

## Proof sketch

When both types use the same undirected graph under neutral drift, the fixation probability of a site equals its reproductive value, and these values average to $1/N$ over a uniform start; this is the baseline that a difference in dispersal perturbs. With two graphs, a mutant whose offspring spread to more distinct sites loses fewer offspring to replacing fellow mutants, which is why denser $G_A$ usually helps. All small-graph statements follow from solving the $2^N$ absorption equations exactly (the source enumerates all 112 connected graphs on 6 vertices against $K_6$).

## Sources

- J. Tkadlec, K. Kaveh, K. Chatterjee, M. A. Nowak, "Evolutionary dynamics of mutants that modify population structure", Journal of the Royal Society Interface (2023), <https://doi.org/10.1098/rsif.2023.0355> (PMC10684346).
