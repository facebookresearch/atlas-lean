# Likelihood-ratio trimming and iterative masking of recombination blocks

Let $r$ be a candidate recombination block on branch $B$ (a run of significant windows from the binomial scan), of length $l_r$ containing $s_r$ substitutions, and let $d_{0,B}$ be the background substitution density over $g$ called bases. The alternative hypothesis $H_{1,B,r}$ models the block as $\mathrm{Binomial}(l_r, d_{1,B,r})$ with $d_{1,B,r} = s_r / l_r$. The block is processed as follows.

1. **Trim.** Shrink $r$ so that its ends are its outermost substitutions, then alternately move the left and right ends inward to the next substitution while doing so increases the likelihood of the block under $H_{1,B,r}$ relative to $H_{0,B}$.
2. **Genome-wide test.** With final length $l_f$ and $s_f$ substitutions, keep the block only if

$$1 - \sum_{i = 0}^{s_f - 1} \binom{l_f}{i}\, d_{0,B}^{\,i}\, (1 - d_{0,B})^{\,l_f - i} \;<\; \frac{0.05}{g / l_f},$$

a Bonferroni correction for the $g / l_f$ non-overlapping windows of that length in the genome.
3. **Mask and iterate.** Among surviving blocks on $B$, take the one with the smallest likelihood ratio $\Pr(r \mid H_{0,B}) / \Pr(r \mid H_{1,B,r})$, convert its span to missing data on $B$ and all descendant nodes, recompute $d_{0,B}$ from the substitutions outside the masked regions, and rescan. Stop when no window rejects $H_{0,B}$ or the minimum number of substitutions needed for significance falls below a set threshold.

After all branches are processed, the phylogeny is re-estimated from the substitutions outside masked regions (the clonal frame), and the procedure repeats until the tree converges.

## Depends on

- [Binomial scan statistic for recombination on a phylogenetic branch](binomial-scan-statistic-for-recombination-on-a-phylogenetic-branch.md)
- [Binomial probability mass function](../../../cancer-genomics/detection-power-for-somatic-mutations/binom-pmf.md)

## Remarks

A run of significant windows may straddle two separate clusters with a sparse gap between them; after trimming, such a merged block can lose significance, and the genome-wide test in step 2 removes it. Masking the most significant block first and re-estimating the background density prevents a large import from inflating $d_{0,B}$ and hiding smaller ones. Turning imported regions into missing data on the descendant subtree keeps vertically inherited point mutations, the signal of common ancestry, as the only input to branch lengths and topology.

## Sources

- N. J. Croucher, A. J. Page, T. R. Connor, A. J. Delaney, J. A. Keane, S. D. Bentley, J. Parkhill, S. R. Harris, "Rapid phylogenetic analysis of large samples of recombinant bacterial whole genome sequences using Gubbins", Nucleic Acids Research 43(3) (2015) e15, Materials and Methods, "Description of algorithm". <https://doi.org/10.1093/nar/gku1196> (PMC4330336)
