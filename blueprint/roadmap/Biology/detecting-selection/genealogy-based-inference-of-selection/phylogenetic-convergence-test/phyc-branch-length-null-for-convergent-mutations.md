# PhyC branch-length null for phenotype-associated convergent mutations

Let a rooted phylogeny with branch set $\mathcal B$ and branch lengths $\ell_b > 0$ be reconstructed for clonal isolates, with an ancestral reconstruction that labels each branch as leading to a phenotype-positive (for example drug-resistant) or phenotype-negative isolate set, $\mathcal B = \mathcal B_R \sqcup \mathcal B_S$. For a target (a nucleotide site, a gene or an intergenic region) the ancestral reconstruction places independent mutation events on branches; suppose $x$ of them fall on resistant branches and $y$ on sensitive branches. The **phylogenetic convergence (PhyC) test** compares $x$ with its distribution under the null model in which the $n = x + y$ events are redistributed over the tree independently, each landing on branch $b$ with probability $\ell_b / L$, $L = \sum_b \ell_b$. Under this null the number $X$ of events on resistant branches is

$$X \sim \mathrm{Binomial}\!\left(n,\; \frac{L_R}{L}\right), \qquad L_R = \sum_{b \in \mathcal B_R} \ell_b,$$

and the one-sided p-value is $\mathbb P(X \ge x)$. Targets with small p-values are inferred to be under positive selection associated with the phenotype.

## Expansion

Conditioning on the observed number $n$ of independent events at the target controls for the target's local mutation rate, and redistributing in proportion to branch length controls for the tree topology and for how the phenotype is distributed over the tree; only the excess of events on phenotype-positive branches carries evidence of selection. Farhat et al. evaluate the null by Monte Carlo (10,000 redistributions) rather than through the binomial closed form, which is exact when each event is placed independently. To limit spurious homoplasy from reconstruction error they keep only high-confidence ancestral calls, require bootstrap support, and count changes between closely related isolates once. Applied to 123 *Mycobacterium tuberculosis* genomes, the test recovered all of a set of known resistance determinants (where $d_N/d_S$ recovered five of eleven) and identified 39 further genomic regions associated with resistance.

## Sources

- M. R. Farhat, B. J. Shapiro, K. J. Kieser, et al., "Genomic analysis identifies targets of convergent positive selection in drug-resistant *Mycobacterium tuberculosis*", Nature Genetics 45 (2013), 1183–1189, <https://doi.org/10.1038/ng.2747> (PMC3887553), Results, description of the PhyC test.
