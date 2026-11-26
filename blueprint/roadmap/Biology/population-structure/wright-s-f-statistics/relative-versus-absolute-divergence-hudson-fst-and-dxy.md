# Relative versus absolute divergence: Hudson's $F_{ST}$ and $d_{XY}$

For two populations $X$ and $Y$ and a genomic region, let $\pi_X$ and $\pi_Y$ be the mean numbers of pairwise differences per site between two sequences drawn within $X$ and within $Y$, let $\pi_W = (\pi_X + \pi_Y)/2$, and let the absolute divergence

$$d_{XY} = \pi_B$$

be the mean number of differences per site between one sequence from $X$ and one from $Y$. Hudson's fixation index is

$$F_{ST} = 1 - \frac{\pi_W}{\pi_B} = \frac{d_{XY} - \pi_W}{d_{XY}}.$$

**Consequence.** $F_{ST}$ is a *relative* measure: for fixed $d_{XY} > 0$ it is strictly decreasing in $\pi_W$. Any process that lowers within-population diversity in a region (background selection or a selective sweep acting in both populations, or low recombination) raises $F_{ST}$ there without any change in between-population divergence. Reduced gene flow at a locus, by contrast, lengthens the time to the most recent common ancestor of sequences from the two populations and therefore raises the absolute measure $d_{XY}$. A region of elevated $F_{ST}$ is evidence of a barrier to gene flow only if $d_{XY}$ is also elevated.

## Remarks

Under the infinite-sites model, expected pairwise differences are proportional to expected coalescence times, $E[\pi_W] = 2\mu\,E[T_W]$ and $E[d_{XY}] = 2\mu\,E[T_B]$, so $F_{ST} \approx 1 - E[T_W]/E[T_B]$. Linked selection shortens within-population coalescence times $T_W$ but, after the populations have split, adds little to the between-population time $T_B$, which is dominated by the split time and ancestral diversity; hence it inflates $F_{ST}$ while leaving $d_{XY}$ roughly unchanged or even slightly lower (through reduced ancestral diversity). Loci resistant to introgression instead keep $T_B$ at its full divergence value, increasing $d_{XY}$ relative to the genomic background. Reanalyses of "genomic islands of speciation" found high-$F_{ST}$ windows without elevated $d_{XY}$, consistent with reduced diversity rather than reduced gene flow.

## Depends on

- [Mean number of pairwise differences](../../coalescent-theory/segregating-sites-and-pairwise-differences/mean-pair-diff.md)

## Sources

- T. E. Cruickshank and M. W. Hahn, "Reanalysis suggests that genomic islands of speciation are due to reduced diversity, not reduced gene flow", Molecular Ecology (2014), <https://doi.org/10.1111/mec.12796>.
- R. R. Hudson, M. Slatkin and W. P. Maddison, "Estimation of levels of gene flow from DNA sequence data", Genetics 132 (1992), 583–589, <https://doi.org/10.1093/genetics/132.2.583>.
