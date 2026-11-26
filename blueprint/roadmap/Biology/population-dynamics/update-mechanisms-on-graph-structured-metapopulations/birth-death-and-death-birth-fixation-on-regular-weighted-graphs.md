# Birth-death and death-birth fixation on regular weighted graphs

Let a population of $N$ individuals occupy the nodes of a graph with nonnegative weights $w_{ij}$, and let $s_i \in \{0, 1\}$ mark a mutant at node $i$, with $n = \sum_i s_i$ mutants. Mutants have relative birth parameter $r > 0$ and relative death parameter $t > 0$ (wild type $1$). Under **Bd updating** an individual is chosen for reproduction with probability proportional to its birth parameter, and its offspring replaces neighbour $j$ of the parent with probability $w_{ij} / \sum_l w_{il}$. Under **Db updating** an individual is chosen to die with probability proportional to its death parameter, and is replaced by the offspring of neighbour $j$ with probability $w_{ij} / \sum_l w_{il}$.

**Proposition (Appendix A.2 of the source).** Suppose the graph is undirected, $w_{ij} = w_{ji}$, and regular, $\sum_l w_{il} = \alpha$ for every $i$. Then from any configuration with $n$ mutants the probability that the mutants fix is

$$\phi_{Bd}(n) = \frac{1 - r^{-n}}{1 - r^{-N}} \quad (r \ne 1), \qquad \phi_{Db}(n) = \frac{1 - t^{n}}{1 - t^{N}} \quad (t \ne 1).$$

In particular Db updating with $t = 1/r$ has the same fixation probability as Bd updating with birth advantage $r$, which is the [Moran fixation probability](../isothermal-theorem-for-evolutionary-graph-dynami/moran-fixation.md) of the well-mixed population.

## Expansion

On a regular graph the one-step transition probabilities of the mutant count are

$$T^{+}_{Bd} = \frac{r \sum_{i,j} w_{ij} s_i (1 - s_j)}{\alpha (r n + N - n)}, \quad T^{-}_{Bd} = \frac{\sum_{i,j} w_{ij} (1 - s_i) s_j}{\alpha (r n + N - n)},$$

and $T^{+}_{Db} = \sum_{i,j} w_{ij} (1 - s_i) s_j / (\alpha (t n + N - n))$, $T^{-}_{Db} = t \sum_{i,j} w_{ij} s_i (1 - s_j) / (\alpha (t n + N - n))$. Symmetry of $w$ makes the two edge sums equal, so $T^-/T^+ = 1/r$ under Bd and $= t$ under Db, independently of the configuration. The mutant count is then a birth-death chain with constant ratio of down to up rates, and the classical gambler's-ruin sum $\phi(n) = \big(1 + \sum_{i=1}^{n-1} \prod_{j \le i} T^-_j/T^+_j\big) / \big(1 + \sum_{i=1}^{N-1} \prod_{j \le i} T^-_j/T^+_j\big)$ gives the formulas. Equal weighted in-degree for Bd is the isothermal condition; the Db statement is its counterpart with selection acting on death.

## Sources

- S. Yagoobi, N. Sharma and A. Traulsen, *Categorizing update mechanisms for graph-structured metapopulations*, Journal of the Royal Society Interface 20 (2023), 20220769. DOI: <https://doi.org/10.1098/rsif.2022.0769>. PMCID: PMC10015335.
