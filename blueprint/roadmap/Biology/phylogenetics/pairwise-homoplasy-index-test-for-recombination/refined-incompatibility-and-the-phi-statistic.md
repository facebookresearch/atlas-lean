# Refined incompatibility and the pairwise homoplasy index

Let an alignment have sites with character states $\chi_i$, and let $|\chi_i|$ be the number of distinct states at site $i$. For two sites $i, j$ let $l(\chi_i, \chi_j)$ be the minimum number of mutations needed by any tree to explain both sites (their joint maximum-parsimony score). Since every non-ancestral state must arise at least once, $l(\chi_i, \chi_j) \ge (|\chi_i| - 1) + (|\chi_j| - 1)$. The **refined incompatibility score** is

$$\iota(\chi_i, \chi_j) = l(\chi_i, \chi_j) - (|\chi_i| - 1) - (|\chi_j| - 1) \ \ge 0 .$$

The two sites are compatible exactly when $\iota(\chi_i, \chi_j) = 0$. Without recombination, $\iota$ is the minimum number of homoplasies in the history of the two sites.

Restrict to the $n$ parsimony-informative sites (each with at least two states carried by at least two sequences), in alignment order, and let $M = (M_{ij})$ be the $n \times n$ refined incompatibility matrix, $M_{ij} = \iota(\chi_i, \chi_j)$. Given a window width $w$ (in bases) and the proportion $q$ of informative sites, set $k = wq$. The **pairwise homoplasy index** is the mean score over the first $k$ off-diagonals:

$$\Phi_w = \frac{2}{k(2n - k - 1)} \sum_{\substack{1 \le i < j \le n\\ j - i \le k}} M_{ij}.$$

The denominator $k(2n-k-1)/2 = \sum_{d=1}^{k}(n - d)$ is the number of pairs averaged. Small $\Phi_w$ relative to its permutation distribution indicates that nearby sites are more compatible than distant ones, which is evidence of recombination.

## Depends on

- [Four-gamete condition for two sites](../../coalescent-theory/hudson-kaplan-bound-on-recombination-events/four-gametes.md)
- [Small parsimony problem](../small-parsimony-problem/README.md)

## Expansion

For two biallelic sites, $l = 2$ exactly when at most three of the four gametes occur, so $\iota = 0$ iff the [four-gamete condition](../../coalescent-theory/hudson-kaplan-bound-on-recombination-events/four-gametes.md) fails; for multistate sites $\iota$ counts how many extra mutations a pair forces. Under recombination, sites close together share genealogies more often than distant ones, so the local average $\Phi_w$ falls below the average over random site orders. The refined score can be computed in time linear in the number of sequences. The paper uses $w = 100$.

## Sources

- T. C. Bruen, H. Philippe, D. Bryant, "A Simple and Robust Statistical Test for Detecting the Presence of Recombination", Genetics 172 (2006), 2665–2681, <https://doi.org/10.1534/genetics.105.048975> (PMC1456386).
