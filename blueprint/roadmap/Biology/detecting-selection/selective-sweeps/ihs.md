# Unstandardized star-genealogy integrated haplotype score

For real numbers $r$, $T_A$ and $T_D$, the unstandardized integrated haplotype score of the star-genealogy model is

$$\mathrm{iHS}^\star(r, T_A, T_D) = \log \frac{\mathrm{iHH}(r, T_A)}{\mathrm{iHH}(r, T_D)},$$

where $\mathrm{iHH}$ is the [one-sided integrated haplotype homozygosity](ihh.md) of star genealogies of ages $T_A$ (ancestral allele) and $T_D$ (derived allele), with the conventions $x/0 = 0$, $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$. It is the log ratio underlying the integrated haplotype score of Voight et al. (2006), without their standardization within allele-frequency bins; the factor two between the one-sided and two-sided integrals cancels in the ratio.

## Sources

- B. F. Voight, S. Kudaravalli, X. Wen and J. K. Pritchard, *A map of recent positive selection in the human genome*, PLoS Biology 4 (2006), e72.
