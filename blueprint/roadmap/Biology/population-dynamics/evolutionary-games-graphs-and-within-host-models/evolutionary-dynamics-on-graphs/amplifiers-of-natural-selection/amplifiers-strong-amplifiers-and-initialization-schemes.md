# Amplifiers, strong amplifiers and initialization schemes

**Model.** Let $G$ be a graph on $N$ vertices with nonnegative edge weights $w_{ij}$ (directed edges and self-loops $w_{ii}$ allowed) such that every vertex has positive total outgoing weight. Each vertex holds one individual, a resident of fitness $1$ or a mutant of fitness $r > 1$; write $f_i$ for the fitness at vertex $i$. In each step of the **birth–death Moran process**, vertex $i$ is chosen to reproduce with probability $f_i / \sum_k f_k$, an outgoing edge $(i, j)$ is chosen with probability $w_{ij} / \sum_k w_{ik}$, and the offspring replaces the occupant of $j$. Starting from a single mutant, the process is absorbed when all vertices are mutants (fixation) or residents (extinction).

**Temperature.** The temperature of vertex $h$ is

$$t_h = \sum_{i} \frac{w_{ih}}{\sum_j w_{ij}},$$

the expected number of times $h$ is replaced per unit of neutral reproduction; $\sum_h t_h = N$.

**Initialization.** Under *uniform initialization* the first mutant is placed at a uniformly random vertex (mutations arising at a constant rate per site); under *temperature initialization* it is placed at $h$ with probability $t_h / N$ (mutations arising during reproduction). Write $\rho(G, r, \mathrm U)$ and $\rho(G, r, \mathrm T)$ for the corresponding fixation probabilities.

**Definitions.** For the complete graph $K_N$ (the well-mixed population),

$$\rho(K_N, r, \mathrm U) = \rho(K_N, r, \mathrm T) = \frac{1 - 1/r}{1 - 1/r^N} \longrightarrow 1 - \frac1r \qquad (N \to \infty).$$

A graph is a *uniform (temperature) amplifier* if its fixation probability exceeds that of $K_N$ for every $r > 1$. A sequence $G_1, G_2, \dots$ of graphs of increasing size is a **strong amplifier** under a given initialization if $\rho(G_i, r, \cdot) \to 1$ for every fixed $r > 1$.

**Examples.** Every isothermal graph (all $t_h = 1$) has exactly the well-mixed fixation probability, so it neither amplifies nor suppresses. The Star $S_N$ (a centre joined to $N - 1$ leaves) satisfies $\rho(S_N, r, \mathrm U) \to 1 - 1/r^2$, so it is a uniform amplifier, but $\rho(S_N, r, \mathrm T) \to 0$, so it is not a temperature amplifier.

## Depends on

- [Moran Fixation](../../../isothermal-theorem-for-evolutionary-graph-dynami/moran-fixation.md)

## Proof depends on

- [Isothermal theorem, "if" direction](../../../isothermal-theorem-for-evolutionary-graph-dynami/average-fixation-eq-moran-fixation.md)
- [Fixation probability on the Star graph](../amplifiers-of-selection-on-undirected-graphs/fixation-probability-on-the-star-graph.md)

## Remarks

Uniform and temperature initialization can rank the same graph oppositely: the Star's leaves are cold under uniform placement (a leaf mutant is rarely replaced, so it survives long enough to reproduce into the hub), while under temperature placement the first mutant almost surely lands on the hot centre, from which it is overwritten by one of $N-1$ leaves before it spreads. Strong amplification is an asymptotic notion because for fixed $N$ the fixation probability of a single mutant with $r$ close to $1$ stays near the neutral value.

## Sources

- A. Pavlogiannis, J. Tkadlec, K. Chatterjee and M. A. Nowak, "Construction of arbitrarily strong amplifiers of natural selection using evolutionary graph theory", Communications Biology 1 (2018), article 71, Introduction and Methods ("Model", "Initialization scheme", Eqs. (1)–(2), "Amplifiers"), <https://doi.org/10.1038/s42003-018-0078-7>, PMCID PMC6123726.
- J. Tkadlec, A. Pavlogiannis, K. Chatterjee and M. A. Nowak, "Fast and strong amplifiers of natural selection", Nature Communications 12 (2021), article 4009, Results ("Model", "Amplifiers and strong amplifiers", Eqs. (1)–(2)), <https://doi.org/10.1038/s41467-021-24271-w>, PMCID PMC8242091.
