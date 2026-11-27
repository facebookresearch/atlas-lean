# Binomial scan statistic for recombination on a phylogenetic branch

Fix a branch $B$ of a rooted phylogeny on which a joint ancestral reconstruction places $s_B$ base substitutions, and let $g$ be the number of alignment positions called (not missing) on the node below $B$. Under the null hypothesis $H_{0,B}$ that substitutions on $B$ arise by point mutation uniformly over the genome, the substitution density is $d_{0,B} = s_B / g$, and the number $S_w$ of substitutions in any window of $w$ called positions satisfies

$$S_w \sim \mathrm{Binomial}(w, d_{0,B}).$$

The window length $w$ is chosen between $100$ and $10{,}000$ bases so that $w\, d_{0,B} \ge 10$. One window is centered on each of the $s_B$ substitutions, and a window containing $s_w$ substitutions is significant when its one-sided binomial tail is below a Bonferroni threshold,

$$\Pr_{H_{0,B}}(S_w \ge s_w) = \sum_{i = s_w}^{w} \binom{w}{i} d_{0,B}^{\,i} (1 - d_{0,B})^{w - i} < \frac{0.05}{s_B}.$$

Maximal runs of contiguous significant windows are the candidate recombination blocks on $B$.

## Depends on

- [Binomial upper tail probability](../../../cancer-genomics/detection-power-for-somatic-mutations/upper-tail.md)

## Remarks

Homologous recombination in bacteria imports a stretch of divergent DNA in one event, so on the branch where it happened it shows up as a cluster of substitutions far denser than the background. Scanning windows centered on observed substitutions is a nonparametric scan statistic for clusters in a point process along the genome. The Bonferroni correction is for the $s_B$ windows tested on that branch. Windows must be short compared with the genome, and regions of elevated substitution density can also be mutational hotspots or loci under relaxed or positive selection on long branches, which this null cannot distinguish from imports.

## Sources

- N. J. Croucher, A. J. Page, T. R. Connor, A. J. Delaney, J. A. Keane, S. D. Bentley, J. Parkhill, S. R. Harris, "Rapid phylogenetic analysis of large samples of recombinant bacterial whole genome sequences using Gubbins", Nucleic Acids Research 43(3) (2015) e15, Materials and Methods, "Description of algorithm". <https://doi.org/10.1093/nar/gku1196> (PMC4330336)
