# Universality of Moran fixation on random graphs

Run the Moran process on a weighted directed graph $G_n = (V_n, W_n)$ with $n$ vertices: a mutant of fitness $r > 0$ or a resident of fitness $1$ is chosen to reproduce with probability proportional to fitness, and the offspring of the individual at $i$ replaces the individual at $j$ with probability $w_{ij}$ (rows of $W_n$ normalized to sum to $1$). Let $\rho_{G_n}(r)$ be the fixation probability of a single mutant at a uniformly random vertex and $\rho_n(r) = (1 - r^{-1})/(1 - r^{-n})$ the well-mixed value. For a vertex set $S$, let $w_O(S)$ and $w_I(S)$ be the total weight of edges leaving and entering $S$.

**Robust isothermal theorem.** If, for some $0 \le \varepsilon < 1$, every nonempty proper subset $S \subsetneq V_n$ has $w_O(S)$ and $w_I(S)$ equal up to a relative error $\varepsilon$, then $|\rho_{G_n}(r) - \rho_n(r)|$ is bounded by a quantity that depends continuously on $\varepsilon$ and vanishes at $\varepsilon = 0$. The case $\varepsilon = 0$ is the isothermal theorem (doubly stochastic $W_n$ gives exactly $\rho_n(r)$).

**Universality for generalized Erdős–Rényi graphs.** Let the directed edges of $G_n$ be present independently with a fixed probability $p \in (0,1)$, carrying independent weights from a suitable distribution (outgoing weights normalized or not). Then there is a constant $C > 0$, independent of $n$, and constants $\xi, \nu > 0$ such that, with probability greater than $1 - \exp(-\nu(\log n)^{1+\xi})$, the fixation probability $\rho_{G_n}(r)$ is within an error $o(1)$ of $\rho_n(r)$ uniformly in $r > 0$ (the error is controlled by $C$ and $n$). In words: as random population structures become large, their fixation probabilities converge to the well-mixed value, independently of the microscopic edge distribution.

## Depends on

- [Isothermal theorem, "if" direction](average-fixation-eq-moran-fixation.md)
- [Fixation probability of the Moran process](../../population-genetics/moran-model/moran-fixation.md)

## Expansion

The fixation probability depends only on the ratios, over subsets $S$ of mutant positions, of the probability of gaining a mutant to that of losing one; these ratios equal $r\,w_O(S)/w_I(S)$. When every ratio $w_O(S)/w_I(S)$ is within $\varepsilon$ of $1$, a coupling with the well-mixed birth–death chain on the mutant count sandwiches $\rho_{G_n}(r)$ between the well-mixed fixation probabilities at fitness $r(1\pm\varepsilon)$, and the smoothness of $\rho_n$ in $r$ turns this into a bound continuous in $\varepsilon$. For random graphs, large-deviation estimates show that every vertex temperature (sum of incoming weights) concentrates near $1$ and that $w_O(S)$, $w_I(S)$ are of the order of $\min(|S|, n - |S|)$ for every $S$ simultaneously, with failure probability $\exp(-\nu(\log n)^{1+\xi})$; together these verify the robust theorem's hypothesis with $\varepsilon \to 0$. Simulations of small-world (Watts–Strogatz) and directed preferential-attachment graphs show the same Moran-type behaviour, which the source conjectures to be universal for many random graph models; degenerate graphs (one-rooted or disconnected) occur with vanishing probability.

## Sources

- B. Adlam, M. A. Nowak, "Universality of fixation probabilities in randomly structured populations", Scientific Reports (2014), <https://doi.org/10.1038/srep06692> (PMC4209402).
- E. Lieberman, C. Hauert, M. A. Nowak, "Evolutionary dynamics on graphs", Nature 433 (2005) 312–316, <https://doi.org/10.1038/nature03204>.
