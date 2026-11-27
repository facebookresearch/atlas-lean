# Universality of Moran fixation on random graphs

Run the Moran process on a weighted directed graph $G_n = (V_n, W_n)$ with $n$ vertices: a mutant of fitness $r > 0$ or a resident of fitness $1$ is chosen to reproduce with probability proportional to fitness, and the offspring of the individual at $i$ replaces the individual at $j$ with probability $w_{ij}$ (rows of $W_n$ normalized to sum to $1$). Let $\rho_{G_n}(r)$ be the fixation probability of a single mutant at a uniformly random vertex and $\rho_n(r) = (1 - r^{-1})/(1 - r^{-n})$ the well-mixed value (with $\rho_n(1) = 1/n$). For a vertex set $S$, let $w_O(S)$ and $w_I(S)$ be the total weight of edges leaving and entering $S$.

**Robust isothermal theorem.** Assume $G_n$ is strongly connected ($W_n$ is irreducible). If, for some $0 \le \varepsilon < 1$, every nonempty proper subset $S \subsetneq V_n$ satisfies $|w_O(S)/w_I(S) - 1| \le \varepsilon$, then $\sup_{r > 0} |\rho_{G_n}(r) - \rho_n(r)| \le \varepsilon$. In particular, at $\varepsilon = 0$ an irreducible doubly stochastic $W_n$ gives $\rho_{G_n}(r) = \rho_n(r)$ (the isothermal theorem).

**Universality for generalized Erdős–Rényi graphs.** Let the raw directed edge weights $x_{ij}$ ($i \ne j$) be independent draws from a fixed nonnegative distribution $\mu$ independent of $n$ with $\Pr[X > 0] = p > 0$ and stretched-exponential tail $\Pr[X > x] \le C_0 e^{-x^{1/C_0}}$ for all $x > 0$ (Adlam–Nowak Supplementary Information, Definition 2.4, with row-normalized weights $w_{ij} = x_{ij}/\sum_k x_{ik}$; and analogously Definition 4.1 for unnormalized weights). Then there exist constants $C, \xi, \nu > 0$ independent of $n$ such that, with probability greater than $1 - \exp(-\nu(\log n)^{1+\xi})$, $\sup_{r > 0} |\rho_{G_n}(r) - \rho_n(r)| \le C (\log n)^{C + C\xi}/\sqrt{n}$ (main text Eq. (5), SI Theorems 2.1 and 4.2). In words: as random population structures become large, their fixation probabilities converge to the well-mixed value, independently of the microscopic edge distribution.

## Depends on

- [Is Fixation Function](is-fixation-function.md)
- [Isothermal theorem, "if" direction](average-fixation-eq-moran-fixation.md)
- [Fixation probability of the Moran process](../../population-genetics/moran-model/moran-fixation.md)

## Proof sketch

The fixation probability depends only on the ratios, over subsets $S$ of mutant positions, of the probability of gaining a mutant to that of losing one; these ratios equal $r\,w_O(S)/w_I(S)$. When every ratio $w_O(S)/w_I(S)$ is within $\varepsilon$ of $1$, a coupling with the well-mixed birth–death chain on the mutant count sandwiches $\rho_{G_n}(r)$ between the well-mixed fixation probabilities at fitness $r(1\pm\varepsilon)$, and the smoothness of $\rho_n$ in $r$ turns this into a bound continuous in $\varepsilon$. For random graphs, large-deviation estimates show that every vertex temperature (sum of incoming weights) concentrates near $1$ and that $w_O(S)$, $w_I(S)$ are of the order of $\min(|S|, n - |S|)$ for every $S$ simultaneously, with failure probability $\exp(-\nu(\log n)^{1+\xi})$; together these verify the robust theorem's hypothesis with $\varepsilon \to 0$. Simulations of small-world (Watts–Strogatz) and directed preferential-attachment graphs show the same Moran-type behaviour, which the source conjectures to be universal for many random graph models; degenerate graphs (one-rooted or disconnected) occur with vanishing probability.

## Sources

- B. Adlam, M. A. Nowak, "Universality of fixation probabilities in randomly structured populations", Scientific Reports (2014), <https://doi.org/10.1038/srep06692> (PMC4209402).
- E. Lieberman, C. Hauert, M. A. Nowak, "Evolutionary dynamics on graphs", Nature 433 (2005) 312–316, <https://doi.org/10.1038/nature03204>.
