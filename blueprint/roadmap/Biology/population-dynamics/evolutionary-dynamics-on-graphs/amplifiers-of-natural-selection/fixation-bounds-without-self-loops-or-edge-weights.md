# Fixation bounds without self-loops or edge weights

Consider the birth–death Moran process on a graph with $N$ vertices and a single mutant of fitness $r > 1$ among residents of fitness $1$.

**Theorem (temperature initialization).**

1. If the graph has no self-loops (edge weights arbitrary), then $\rho(G, r, \mathrm T) \le 1 - \dfrac{1}{r + 1}$.
2. If the graph is unweighted (self-loops allowed), then $\rho(G, r, \mathrm T) \le 1 - \dfrac{1}{4r + 2}$.

**Theorem (uniform initialization, bounded degree).** Suppose every vertex has at most $c$ incident edges.

3. If the graph has no self-loops (edge weights arbitrary), then $\rho(G, r, \mathrm U) \le 1 - \dfrac{1}{c + c r^2}$.
4. If the graph is unweighted (self-loops allowed), then $\rho(G, r, \mathrm U) \le 1 - \dfrac{1}{1 + r c}$.

Each bound is uniform in $N$, so no family lacking self-loops, or lacking edge weights, is a strong amplifier under temperature initialization, and no such bounded-degree family is a strong amplifier under uniform initialization. Both ingredients are thus necessary for the strong amplifiers built from weighted graphs with self-loops.

## Depends on

- [Amplifiers, strong amplifiers and initialization schemes](amplifiers-strong-amplifiers-and-initialization-schemes.md)
- [Strong amplifiers from weighted graphs with self-loops](strong-amplifiers-from-weighted-graphs-with-self-loops.md)

## Proof sketch

Proof of bound 1. Let the mutant start at $i$, all neighbours residents. Without a self-loop at $i$, the mutant's own reproduction never replaces itself, so in the embedded jump chain it reproduces at relative rate $r$ while it is replaced at relative rate $\sum_k w_{ki}/\sum_j w_{kj} = t_i$. The probability that it is replaced before reproducing even once is therefore $t_i / (t_i + r)$, and

$$\rho(G, r, \mathrm T) \le \sum_i \frac{t_i}{N} \cdot \frac{r}{t_i + r} = \frac1N \sum_i g(t_i), \qquad g(t) = \frac{r t}{t + r}.$$

Because $g$ is concave and the temperatures average to $1$, Jensen's inequality gives $\frac1N \sum_i g(t_i) \le g(1) = r/(r+1) = 1 - 1/(r+1)$. The other three bounds are proved in the source by refinements of the same early-extinction estimate: a mutant that is likely to be replaced before it first reproduces is likely to go extinct.

## Sources

- A. Pavlogiannis, J. Tkadlec, K. Chatterjee and M. A. Nowak, "Construction of arbitrarily strong amplifiers of natural selection using evolutionary graph theory", Communications Biology 1 (2018), article 71, Results ("Necessary conditions for amplification") and Methods ("Necessary conditions for amplification"); proofs in Supplementary Note 1, Section 4, <https://doi.org/10.1038/s42003-018-0078-7>, PMCID PMC6123726.
