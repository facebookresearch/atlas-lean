# iSAFE score aggregated over windows

Let a large region (megabases) be covered by a set $W$ of overlapping windows of a fixed number of SNPs (for example $300$ SNPs with $50\%$ overlap). In each window compute the SAFE score of its own mutations and let $S_1$ be the set of the top-scoring mutation of each window. For a mutation $e$ and a window $w$, let $\Psi_{e,w} = \max\{\mathrm{SAFE}_w(e), 0\}$, where $\mathrm{SAFE}_w(e)$ is the SAFE score of $e$ after inserting site $e$ into the haplotypes of window $w$. Define the window weights and the **iSAFE score**

$$\alpha(w) = \frac{\sum_{e \in S_1} \Psi_{e,w}}{\sum_{w' \in W} \sum_{e \in S_1} \Psi_{e,w'}}, \qquad \mathrm{iSAFE}(e) = \sum_{w \in W} \Psi_{e,w}\, \alpha(w),$$

for every mutation $e$ of the region, including those outside $S_1$. Mutations are ranked by iSAFE. When the favored allele is near fixation (derived frequency $D_T > 0.9$ in the target population) and its maximum difference in derived allele frequency $\mathrm{MDDAF} = D_T - \min D_{NT}$ over non-target populations exceeds a calibrated cutoff ($0.78$ for human demography), outgroup haplotypes are added to make up $10\%$ of the sample so that the frequency is no longer at the boundary.

## Depends on

- [SAFE score from haplotype allele frequency scores](safe-score-from-haplotype-allele-frequency-scores.md)

## Expansion

Recombination gives different windows different genealogies. Inserted into a window whose genealogy matches its own, the favored mutation separates the window's carrier haplotypes (with elevated HAF scores) from non-carriers and gets a high SAFE score; a non-favored mutation inserted into an unrelated window does not. Windows in the sweep's shoulders, which share the favored mutation's genealogy, therefore receive high weights $\alpha(w)$, and summing $\Psi_{e,w}$ with these weights lets the shoulders vote for the favored mutation instead of diluting it. Since $\alpha$ sums to one, iSAFE scores are normalized and comparable across samples, but they are not derived from a likelihood, so significance is assessed against neutral simulations. On simulated $5$ Mb regions under a human demographic model the favored mutation was ranked within the top $20$ in $94\%$ of cases, versus $35\%$ for the composite of multiple signals (CMS).

## Sources

- A. Akbari, J. J. Vitti, A. Iranmehr, M. Bakhtiari, P. C. Sabeti, S. Mirarab and V. Bafna, "Identifying the favored mutation in a positive selective sweep", *Nature Methods* 15 (2018), Online Methods Eqs. (4)–(6), <https://doi.org/10.1038/nmeth.4606> (PMC6231406).
