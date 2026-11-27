# Allele-specific copy number from logR and BAF under purity and ploidy

Let a tumour sample have purity $\rho \in (0, 1]$ and cancer-cell ploidy $\psi > 0$, with diploid normal cells heterozygous at a site, and let the cancer cells carry $n_1$ copies of allele 1 and $n_2$ copies of allele 2 there. Assume the total copy number at the site is positive, $\rho(n_1 + n_2) + 2(1 - \rho) > 0$, which holds automatically when $\rho < 1$; for a pure tumour ($\rho = 1$) it excludes $n_1 = n_2 = 0$, where the site yields no reads, so $\mathrm{logR} = -\infty$ and BAF is undefined. In the noise-free model the coverage ratio relative to the sample average and the fraction of reads from allele 1 are

$$2^{\mathrm{logR}} = \frac{\rho(n_1 + n_2) + 2(1 - \rho)}{\rho \psi + 2(1 - \rho)}, \qquad \mathrm{BAF} = \frac{\rho n_1 + (1 - \rho)}{\rho (n_1 + n_2) + 2(1 - \rho)}.$$

Then $(n_1, n_2)$ is uniquely determined by $(\mathrm{logR}, \mathrm{BAF})$ on this domain:

$$n_1 = \frac{\rho - 1 + \mathrm{BAF} \cdot 2^{\mathrm{logR}} \big(2(1 - \rho) + \rho \psi\big)}{\rho}, \qquad n_2 = \frac{\rho - 1 - (\mathrm{BAF} - 1) \cdot 2^{\mathrm{logR}} \big(2(1 - \rho) + \rho \psi\big)}{\rho},$$

and in particular $n_1 + n_2 = \big(2^{\mathrm{logR}}(2(1 - \rho) + \rho\psi) - 2(1 - \rho)\big)/\rho$.

Applied to measured data the formulas give real-valued estimates. In LOHHLA, logR is computed in 150 bp bins over both homologous HLA alleles as the tumour/normal coverage ratio times the ratio of uniquely mapped germline to tumour reads, BAF is computed at each site where the two HLA alleles differ, the two copy numbers are summarized by their medians across bins, and an allele with estimated copy number below $0.5$ is called lost.

## Depends on

- [Average absolute copy number of a tumor sample](../tumour-purity-ploidy-and-copy-ratio-algebra/mix-copy.md)
- [Relative copy ratio](../tumour-purity-ploidy-and-copy-ratio-algebra/copy-ratio.md)
- [Expected allelic fraction of a germline variant](../tumour-purity-ploidy-and-copy-ratio-algebra/germline-af.md)

## Proof sketch

Write $D_\psi = \rho\psi + 2(1 - \rho)$ for the average copy number of the sample. Multiplying the two model equations gives $\mathrm{BAF} \cdot 2^{\mathrm{logR}} D_\psi = \rho n_1 + (1 - \rho)$, which is linear in $n_1$; likewise $(1 - \mathrm{BAF})\, 2^{\mathrm{logR}} D_\psi = \rho n_2 + (1 - \rho)$. Solving each for the copy number gives the formulas, and since $\rho > 0$ the map $(n_1, n_2) \mapsto (\mathrm{logR}, \mathrm{BAF})$ is injective on the region where the total copy number of the sample is positive. Error in the purity and ploidy inputs propagates linearly through $D_\psi/\rho$, and a $1/\rho$ factor inflates noise at low purity, which is why the loss call is paired with a test for allelic imbalance between the two homologs.

## Sources

- N. McGranahan et al., "Allele-specific HLA loss and immune escape in lung cancer evolution", Cell 171 (2017), 1259–1271, STAR Methods (LOHHLA algorithm, Steps 4–5), <https://doi.org/10.1016/j.cell.2017.10.001>, PMCID: PMC5720478.
