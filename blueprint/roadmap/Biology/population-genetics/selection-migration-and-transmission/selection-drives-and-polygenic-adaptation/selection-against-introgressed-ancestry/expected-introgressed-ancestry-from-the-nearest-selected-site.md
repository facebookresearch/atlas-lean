# Expected introgressed ancestry from the nearest selected site

Fix a neutral site $\ell$ and the $I_\ell$ exons within a window around it (the paper uses 1 cM), ordered by distance; exon $i$ has length $l_i$ base pairs and recombination fraction $r_i$ to $\ell$ (measured to its centre). Each exonic base is independently under purifying selection with probability $\mu$, and with $\mu l_i \ll 1$ exon $i$ contains a selected site with probability about $\mu l_i$. When $\mu$ and the selection coefficient $s$ are small, only the nearest selected site matters. With $f(r,s,t)$ the single-locus factor of the [gene flow factor model](gene-flow-factor-after-a-single-admixture-pulse.md), the expected frequency at $\ell$ of a neutral allele introgressed at frequency $p_0$ is $E[p_{t,\ell}] = p_0\,g_\ell(r,s,t,\mu)$ with

$$g_\ell(r,s,t,\mu) = \sum_{i=1}^{I_\ell}\mu l_i\prod_{j=1}^{i-1}(1 - \mu l_j)\;f(r_i, s, t) + \prod_{j=1}^{I_\ell}(1 - \mu l_j).$$

**Least-squares fit.** Given observed introgressed-allele frequencies $p_{\ell,n}$ at $n_l$ sites, minimize

$$\mathrm{RSS}(p_0, s, \mu) = \sum_{\ell=1}^{n_l}\bigl(p_{\ell,n} - p_0\,g_\ell(r,s,t,\mu)\bigr)^2.$$

For fixed $(s,\mu)$ the minimizing initial frequency is explicit,

$$p_{0,\min}(s,\mu) = \frac{\sum_\ell p_{\ell,n}\,g_\ell}{\sum_\ell g_\ell^2},$$

so only $(s,\mu)$ need a grid search; confidence intervals come from a block bootstrap over genome segments.

## Proof sketch

The weight $\mu l_i\prod_{j<i}(1-\mu l_j)$ is the probability that exon $i$ holds the nearest selected site (none of the $i-1$ closer exons does, and exon $i$ does), and the final product is the probability that no exon in the window is selected, in which case the neutral allele keeps its initial frequency. The fit is linear in $p_0$, so for each $(s,\mu)$ the RSS is a quadratic in $p_0$ minimized at the displayed ratio. Applied to genome-wide Neanderthal ancestry maps, the fit indicates that purifying selection acted mostly on many weakly deleterious alleles, and that East Asians had somewhat higher initial Neanderthal ancestry than Europeans even after accounting for selection; the same machinery with the X-linked factor $f_X$ applies to the X chromosome, where the parameters are more strongly confounded.

## Depends on

- [Gene flow factor after a single admixture pulse](gene-flow-factor-after-a-single-admixture-pulse.md)

## Sources

- I. Jurić, S. Aeschbacher and G. Coop, "The strength of selection against Neanderthal introgression", PLoS Genetics 12 (2016), e1006340, Methods ("Model", Equations 1–5; "Inference procedure", Equations 6–7), <https://doi.org/10.1371/journal.pgen.1006340> (PMC5100956).
