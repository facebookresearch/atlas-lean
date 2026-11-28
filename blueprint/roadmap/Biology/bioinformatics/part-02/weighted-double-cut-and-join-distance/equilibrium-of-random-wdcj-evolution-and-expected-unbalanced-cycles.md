# Equilibrium of random wDCJ evolution and expected unbalanced cycles

Consider the Markov chain on weighted genomes (perfect matchings on $2n$ extremities with nonnegative edge weights) in which each step picks two edges $ab$, $cd$ uniformly at random, reconnects them by a DCJ, draws $x$ uniformly in $[0, w(ab)]$ and $y$ uniformly in $[0, w(cd)]$, and assigns weight $x + y$ to one new edge and $w(ab) + w(cd) - x - y$ to the other, each with probability $1/2$.

(1) The equilibrium distribution of this chain gives a genome $g$ probability proportional to $\prod_{e \in E(g)} w(e)$. Consequently, at equilibrium the weight vector follows a symmetric Dirichlet law with parameter $2$: an equilibrium genome is a uniformly random perfect matching with independent Gamma-distributed weights of shape $2$, rescaled to the total weight.

(2) If $k$ random wDCJ are applied to a weighted genome $g_1$ with $n$ edges to produce $g_2$, the expected number of unbalanced cycles in $BG(g_1, g_2)$ satisfies

$$E(n_u) = O\!\left(\frac{k}{\sqrt n}\right).$$

Since the exact wDCJ distance can be computed in $O^*(3^{n_u})$ time, this bound explains why the exact algorithms remain fast on genomes that evolved by moderately many rearrangements.

## Depends on

- [wDCJ distance formula and its complexity](wdcj-distance-formula-and-its-complexity.md)

## Expansion

For part 1, one checks detailed balance: when $g_1$ and $g_2$ differ by one reconnection, the forward and backward transition probabilities are ratios of edge weights such that $\Pi(g_1)P(g_1, g_2) = \Pi(g_2)P(g_2, g_1)$ for $\Pi(g) \propto \prod_e w(e)$. For part 2, split unbalanced cycles by size at threshold $s = \sqrt n$. Each large unbalanced cycle forces at least $s$ operations by the distance formula, so there are at most $k/\sqrt n$ of them. A small cycle arises from a split that produces a cycle of size below $s$, which has probability $O(s/n)$ per step among the $O(n^2)$ possible operations, giving an expected $O(ks/n) = O(k/\sqrt n)$ small unbalanced cycles.

## Sources

- G. Fertin, G. Jean and E. Tannier, "Algorithms for computing the double cut and join distance on both gene order and intergenic sizes", *Algorithms for Molecular Biology* 12 (2017), section "A probabilistic model of evolution by wDCJ", Proposition 13 and Theorem 14. <https://doi.org/10.1186/s13015-017-0107-y> (PMC5460591)
