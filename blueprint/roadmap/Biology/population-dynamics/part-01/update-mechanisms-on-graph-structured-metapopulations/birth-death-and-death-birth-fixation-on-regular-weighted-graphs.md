# Birth-death and death-birth fixation on regular weighted graphs

Let a population of $N$ individuals occupy the nodes of a graph with nonnegative weights $w_{ij}$, and let $s_i \in \{0, 1\}$ mark a mutant at node $i$, with $n = \sum_i s_i$ mutants. Mutants have relative birth parameter $r > 0$ and relative death parameter $t > 0$ (wild type $1$). Under **Bd updating** an individual is chosen for reproduction with probability proportional to its birth parameter, and its offspring replaces neighbour $j$ of the parent with probability $w_{ij} / \sum_l w_{il}$. Under **Db updating** an individual is chosen to die with probability proportional to its death parameter, and is replaced by the offspring of neighbour $j$ with probability $w_{ij} / \sum_l w_{il}$.

**Proposition (Appendix A.2 of the source).** Suppose $N \ge 2$, the graph is undirected, $w_{ij} = w_{ji}$, regular with a positive common row sum, $\sum_l w_{il} = \alpha > 0$ for every $i$, and connected: the graph with an edge $\{i, j\}$ whenever $w_{ij} > 0$ is connected. Then from any configuration with $n$ mutants, $0 \le n \le N$, the probability that the mutants fix is

$$\phi_{Bd}(n) = \frac{1 - r^{-n}}{1 - r^{-N}} \quad (r \ne 1), \qquad \phi_{Db}(n) = \frac{1 - t^{n}}{1 - t^{N}} \quad (t \ne 1).$$

In particular Db updating with $t = 1/r$ has the same fixation probability as Bd updating with birth advantage $r$, which is the [fixation probability of the well-mixed Moran process](../../../population-genetics/moran-model/moran-fixation.md) started from $n$ mutants.

Connectedness cannot be dropped: for two disjoint unit-weight edges, one entirely mutant and the other entirely wild type, the graph is undirected and regular, yet global fixation has probability $0$, while the Bd formula with $N = 4$, $n = 2$, $r = 2$ gives $4/5$.

## Depends on

- [Fixation probability of the Moran process](../../../population-genetics/moran-model/moran-fixation.md)

## Expansion

On a regular graph the one-step transition probabilities of the mutant count are

$$T^{+}_{Bd} = \frac{r \sum_{i,j} w_{ij} s_i (1 - s_j)}{\alpha (r n + N - n)}, \quad T^{-}_{Bd} = \frac{\sum_{i,j} w_{ij} (1 - s_i) s_j}{\alpha (r n + N - n)},$$

and $T^{+}_{Db} = \sum_{i,j} w_{ij} (1 - s_i) s_j / (\alpha (t n + N - n))$, $T^{-}_{Db} = t \sum_{i,j} w_{ij} s_i (1 - s_j) / (\alpha (t n + N - n))$. Symmetry of $w$ makes the two edge sums equal; in a mixed configuration ($0 < n < N$) connectedness makes this common cut weight positive, so $T^-/T^+ = 1/r$ under Bd and $= t$ under Db, independently of the configuration. Hence $r^{-n}$ under Bd (and $t^{n}$ under Db), evaluated at the current mutant count, is a bounded martingale. Connectedness and $\alpha > 0$ also make absorption at $n = 0$ or $n = N$ certain, and optional stopping gives $\phi(n)\,c^{N} + (1 - \phi(n)) = c^{n}$ with $c = r^{-1}$ or $c = t$, which is the stated formula. The mutant count alone need not be a Markov chain; only the ratio of its up and down probabilities is constant. Equal weighted in-degree for Bd is the isothermal condition, which requires irreducibility as well; the Db statement is its counterpart with selection acting on death.

## Sources

- S. Yagoobi, N. Sharma and A. Traulsen, *Categorizing update mechanisms for graph-structured metapopulations*, Journal of the Royal Society Interface 20 (2023), 20220769. DOI: <https://doi.org/10.1098/rsif.2022.0769>. PMCID: PMC10015335.
