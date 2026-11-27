# Power-law calibration of cell-type enrichment scores

Let $A \in \mathbb{R}^{C \times N}$ hold raw enrichment scores of $C$ cell types in $N$ bulk expression samples, where $A_{ij}$ is the average, over the gene signatures assigned to cell type $i$, of the single-sample gene-set enrichment scores of sample $j$. Raw scores of different cell types are not on a common scale, and in sequencing data they are not linear in the underlying abundance. For each cell type $i$ fix three learned constants: a power $P_i > 0$, a slope $V_{1,i} > 0$ and a scale $V_{2,i} > 0$. The calibrated score is

$$T_{ij} = \frac{\bigl((A_{ij} - \min_{k} A_{ik})/5000\bigr)^{P_i}}{V_{1,i}\, V_{2,i}}, \qquad 1 \le i \le C,\ 1 \le j \le N.$$

The constants are learned from synthetic mixtures in which cell type $i$ is present at known fractions $f$ against a control cell type:

1. shift the scores so the lowest mixture fraction scores $0$ and divide by $5000$;
2. fit a power function to the shifted scores $s(f)$ over the low-abundance range $0.8\% \le f \le 25.6\%$ and average the fitted power coefficient across reference data sources, giving $P_i$;
3. regress the power-adjusted scores $s^{P_i}$ linearly on $f$ and take the slope as $V_{1,i}$;
4. take $V_{2,i}$ from the diagonal of the uncompensated spillover matrix, the calibrated score of cell type $i$ in a mixture containing $25\%$ of cell type $i$.

After this transform, $T_{ij}$ is approximately linear in the abundance of cell type $i$ in sample $j$ and is on the same scale for every $i$, which is the precondition for compensating between cell types.

## Remarks

Enrichment scores rank genes within a sample, so their distribution depends on signature size and composition: two signatures detecting the same cell fraction can return very different raw values. The minimum shift removes the per-signature offset; the power transform straightens the curved dose-response relation seen in sequencing data; the two divisors put every cell type on a common unit. The fit is restricted to fractions up to $25.6\%$ because the method targets detection of rare cell types and the curve bends steeply above that range. Separate constants are learned for sequencing-based and microarray-based inputs.

## Sources

- D. Aran, Z. Hu, A. J. Butte, "xCell: digitally portraying the tissue cellular heterogeneity landscape", Genome Biology 18 (2017) 220, Methods, "Learning parameters for raw score transformation" and "Calculating scores for a mixture", step (3). <https://doi.org/10.1186/s13059-017-1349-1> (PMC5688663)
