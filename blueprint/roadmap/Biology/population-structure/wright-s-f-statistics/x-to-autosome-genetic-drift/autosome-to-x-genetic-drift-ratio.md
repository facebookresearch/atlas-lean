# Autosome-to-X genetic drift ratio

Let populations $A$ and $B$ split from a common ancestor, and let SNPs be ascertained as heterozygous in two chromosomes sampled from $A$. Assume $A$ has had effectively constant size since the split. On the autosomes let $\tau_A, \tau_B \ge 0$ be the scaled drift times (generations divided by twice the effective size) on the two branches since the split. Then the expected differentiation of ascertained SNPs is

$$\mathbb{E}\bigl(F_{ST}^{\mathrm{auto}}\bigr) = \frac{1 - e^{-(\tau_A + \tau_B)}}{2},$$

independently of size changes in $B$. If the ratio of X-chromosome to autosome effective size is $\rho = N_e^X / N_e^{\mathrm{auto}}$, the X-chromosome drift times are $\tau_A/\rho$ and $\tau_B/\rho$, so

$$\mathbb{E}\bigl(F_{ST}^{X}\bigr) = \frac{1 - e^{-(\tau_A + \tau_B)/\rho}}{2}, \qquad Q := \frac{\ln\bigl(1 - 2\,\mathbb{E}(F_{ST}^{\mathrm{auto}})\bigr)}{\ln\bigl(1 - 2\,\mathbb{E}(F_{ST}^{X})\bigr)} = \rho .$$

With equal numbers of breeding females and males, $\rho = 3/4$, so a neutral population of balanced sex ratio has autosome-to-X drift ratio $Q = 3/4$. A ratio $Q < 3/4$ indicates accelerated drift on the X chromosome (for example a reduced female effective size, or selection acting on the X); $Q > 3/4$ indicates the reverse.

## Depends on

- [Effective size for an X-linked locus](../../../population-genetics/effective-population-size/effective-size-for-x-linked-loci.md)

## Expansion

Since $1 - 2\,\mathbb{E}(F_{ST}) = e^{-\text{(total scaled drift)}}$, the logarithm turns each expectation into minus the total scaled drift time on the two branches, and the ratio cancels the unknown calendar times, leaving the effective-size ratio. With $N_f$ females and $N_m$ males, the X-linked effective size $9N_fN_m/(4N_m + 2N_f)$ divided by the autosomal effective size $4N_fN_m/(N_f + N_m)$ gives $\rho = 9(N_f + N_m)/\bigl(8(2N_m + N_f)\bigr)$, which equals $3/4$ when $N_f = N_m$, rises towards $9/8$ when effective males are few (as under polygyny) and falls towards $9/16$ when effective females are few. In the same way, the expected pairwise coalescence time on the X is $\rho$ times that on the autosomes in a population of constant size. Applied to genome-scale data, the source found $Q = 0.582 \pm 0.030$ between North Europeans and West Africans and $0.615 \pm 0.030$ between East Asians and West Africans, but $Q$ consistent with $3/4$ between North Europeans and East Asians, locating a period of accelerated X drift in the ancestral non-African population.

## Sources

- A. Keinan, J. C. Mullikin, N. Patterson and D. Reich, "Accelerated genetic drift on chromosome X during the human dispersal out of Africa", *Nature Genetics* 41 (2009), 66–70, Methods section "Allele frequency differentiation analysis" and Table 1, <https://doi.org/10.1038/ng.303> (PMC2612098).
