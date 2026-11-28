# Fixation bounds without self-loops or edge weights

Consider the birth–death Moran process on a graph with $N$ vertices and a single mutant of fitness $r > 1$ among residents of fitness $1$.

**Theorem (temperature initialization).**

1. If the graph has no self-loops (edge weights arbitrary), then $\rho(G, r, \mathrm T) \le 1 - \dfrac{1}{r + 1}$.
2. If the graph is unweighted (self-loops allowed), then $\rho(G, r, \mathrm T) \le 1 - \dfrac{1}{4r + 2}$.

**Theorem (uniform initialization, bounded degree).** Suppose every vertex has at most $c$ incident edges.

3. If the graph has no self-loops (edge weights arbitrary), then $\rho(G, r, \mathrm U) \le 1 - \dfrac{1}{c + r c^2}$.
4. If the graph is unweighted (self-loops allowed), then $\rho(G, r, \mathrm U) \le 1 - \dfrac{1}{1 + r c}$.

**Correction of bound 3.** The main text of the source prints this bound as $1 - 1/(c + cr^2)$ (Results, "Necessary conditions for amplification", and Methods), which is a misprint. Supplementary Note 1, Section 4, Theorem 3, states "$\rho(G_n, r, U) \le 1 - 1/(c + r\cdot c^2)$", and its summary in Section 2.2 gives "$1 - 1/(c + c^2 r)$". The main text's own outline also yields this form: at least $N/c$ vertices are hot, and from a hot vertex the mutant goes extinct with probability at least $1/(1 + rc)$, so $\rho \le 1 - \frac1c\cdot\frac{1}{1 + rc} = 1 - \frac{1}{c + rc^2}$. Supplementary Note 1 states Theorems 1–4 for every $r \ge 1$.

Each bound is uniform in $N$, so no family lacking self-loops, or lacking edge weights, is a strong amplifier under temperature initialization, and no such bounded-degree family is a strong amplifier under uniform initialization. Both ingredients are thus necessary for the strong amplifiers built from weighted graphs with self-loops.

## Depends on

- [Amplifiers, strong amplifiers and initialization schemes](amplifiers-strong-amplifiers-and-initialization-schemes.md)
- [Strong amplifiers from weighted graphs with self-loops](strong-amplifiers-from-weighted-graphs-with-self-loops.md)

## Proof sketch

Proof of bound 1. Let the mutant start at $i$, all neighbours residents. Without a self-loop at $i$, the mutant's own reproduction never replaces itself, so in the embedded jump chain it reproduces at relative rate $r$ while it is replaced at relative rate $\sum_k w_{ki}/\sum_j w_{kj} = t_i$. The probability that it is replaced before reproducing even once is therefore $t_i / (t_i + r)$, and

$$\rho(G, r, \mathrm T) \le \sum_i \frac{t_i}{N} \cdot \frac{r}{t_i + r} = \frac1N \sum_i g(t_i), \qquad g(t) = \frac{r t}{t + r}.$$

Because $g$ is concave and the temperatures average to $1$, Jensen's inequality gives $\frac1N \sum_i g(t_i) \le g(1) = r/(r+1) = 1 - 1/(r+1)$. The other three bounds are proved in the companion proofs preprint by refinements of the same early-extinction estimate: a mutant that is likely to be replaced before it first reproduces is likely to go extinct.

## Sources

- A. Pavlogiannis, J. Tkadlec, K. Chatterjee and M. A. Nowak, "Construction of arbitrarily strong amplifiers of natural selection using evolutionary graph theory", Communications Biology 1 (2018), article 71, Results ("Necessary conditions for amplification") and Methods ("Necessary conditions for amplification"); Supplementary Note 1, Section 4, Theorems 1–4 and Corollaries 1–4 (Theorem 3 gives the corrected form of bound 3), <https://doi.org/10.1038/s42003-018-0078-7>, PMCID PMC6123726.
- A. Pavlogiannis, J. Tkadlec, K. Chatterjee and M. A. Nowak, "Strong amplifiers of natural selection: Proofs", arXiv:1802.02509 (2018), <https://arxiv.org/abs/1802.02509>, cited by Supplementary Note 1 for the full proofs of Theorems 1–4.
