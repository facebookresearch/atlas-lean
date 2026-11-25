# Polynomial method for quantum query complexity

After $T$ queries to an input $x \in \{0,1\}^N$, every amplitude of the final state of a quantum query
algorithm is a multilinear polynomial in $x_1, \dots, x_N$ of degree at most $T$, so its acceptance
probability is a real multilinear polynomial of degree at most $2T$. Consequently, if the algorithm computes
$f$ with error at most $\varepsilon$ then $T \ge \widetilde{\deg}_\varepsilon(f)/2$, where
$\widetilde{\deg}_\varepsilon(f)$ is the $\varepsilon$-approximate degree of $f$, and every exact algorithm uses
at least $\deg(f)/2$ queries.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Quantum query (oracle) model.

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §11.2. <https://arxiv.org/pdf/1907.09415v6>
