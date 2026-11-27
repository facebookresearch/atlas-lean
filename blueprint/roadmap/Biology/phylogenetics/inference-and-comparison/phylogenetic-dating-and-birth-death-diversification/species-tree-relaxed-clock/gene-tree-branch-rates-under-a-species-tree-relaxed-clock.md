# Gene-tree branch rates under a species-tree relaxed clock

Let a gene tree be embedded in a dated species tree, let locus $g$ have clock rate $c_g > 0$, and let species-tree branch $j$ carry a relative rate $R_j > 0$. Consider a gene-tree branch of total duration $l > 0$ that spends time $L_j \ge 0$ inside species-tree branch $j$, so that $\sum_j L_j = l$. Under the species-tree relaxed clock, substitutions accumulate at rate $c_g R_j$ while the lineage is in branch $j$, so the expected number of substitutions per site along the gene-tree branch is

$$\Sigma E(S) \;=\; c_g \sum_j R_j\, L_j,$$

and the effective rate assigned to the gene-tree branch is

$$r \;=\; \frac{\Sigma E(S)}{l} \;=\; c_g\,\frac{\sum_j R_j L_j}{\sum_j L_j},$$

the clock rate times the time-weighted mean of the species-branch rates traversed. Consequently $c_g \min_j R_j \le r \le c_g \max_j R_j$, and $r = c_g R_j$ when the branch lies inside a single species branch. In the worked example of the source, a gene branch of duration $1.5$ that accumulates $0.00135$ expected substitutions per site across the species branches it traverses has rate $0.00135/1.5 = 0.0009$.

## Depends on

- [Gene-tree density under the multispecies coalescent](../../../../coalescent-theory/multispecies-coalescent/gene-tree-prob.md)

## Expansion

Within each species branch the substitution process runs at constant rate $c_g R_j$, so expected substitutions add over the segments of the gene branch, and dividing by duration gives the mean rate; the bounds hold because a weighted average lies between its extreme values. The model uses one parameter per species branch shared by all loci, rather than one per branch of every gene tree, and the $R_j$ can follow any branch-rate prior (uncorrelated lognormal, uncorrelated exponential or random local clocks). Ignoring incomplete lineage sorting biases rate estimates: gene lineages coalesce deeper than speciation, which inflates the apparent lengths of short species branches, so concatenation infers spurious rate variation even from data simulated under a strict clock, whereas the species-tree relaxed clock recovers the true rates.

## Sources

- H. A. Ogilvie, R. R. Bouckaert, A. J. Drummond, "StarBEAST2 brings faster species tree inference and accurate estimates of substitution rates", *Molecular Biology and Evolution* 34(8) (2017) 2101–2114, New Approaches, "Species Tree Relaxed Clocks" (Equations (7)–(8), Figure 1 and Table 1), and Results, "Species Tree Relaxed Clocks Prevent SPILS", <https://doi.org/10.1093/molbev/msx126> (PMC5850801).
