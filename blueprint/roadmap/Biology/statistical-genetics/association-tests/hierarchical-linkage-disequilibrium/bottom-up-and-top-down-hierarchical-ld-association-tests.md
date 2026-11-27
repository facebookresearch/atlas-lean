# Bottom-up and top-down hierarchical LD association tests

**Setting.** In a case–control study with genotypes at $M$ biallelic loci, let $\delta^{ca}=(\delta^{ca}_s)_{s\in S}$ and $\delta^{co}=(\delta^{co}_s)_{s\in S}$ be the joint-cumulant parameters (allele frequencies, pairwise LD, higher-order LD) of the haplotype distributions of cases and controls, $S$ the nonempty subsets of loci, and $\Delta$ the parameter space. The likelihood of unphased genotypes under Hardy–Weinberg equilibrium is $L_0(G;\theta)=\prod_i\sum_{(h_1,h_2)\in S(G_i)}\theta_{h_1}\theta_{h_2}$ in each group.

**Full test.** $H_0:\delta^{ca}=\delta^{co}$ against an unrestricted alternative in $\Delta^2$. The likelihood-ratio statistic is asymptotically $\chi^2_{2^M-1}$ under $H_0$; this is the standard global haplotype test rewritten in LD parameters.

**Bottom-up tests.** For a set $P$ of orders (e.g. $P=\{1,2\}$),

$$H_0^{BU,P}:\ \delta^{ca}_s=\delta^{co}_s\ \text{ for all } s\in S \text{ with } |s|\in P,\qquad H_1:\ \text{unrestricted}.$$

Only the parameters of orders in $P$ are constrained, so the test has $\sum_{k\in P}\binom Mk$ degrees of freedom.

**Top-down tests.** For a set $P$ of orders (e.g. $P=\{2,3\}$ when $M=3$),

$$H_0:\ \delta^{ca}=\delta^{co},\qquad H_1^{TD,P}:\ \delta^{ca}_s=\delta^{co}_s\ \text{ for all } s \text{ with } |s|\notin P.$$

Only parameters of orders in $P$ may differ under the alternative.

Both families keep the order-by-order structure: lower-order parameters are estimated first and higher-order ones honour the constraints automatically, so maximum-likelihood fits under null and alternative use the same direct single-parameter optimizations. Constraining higher orders while freeing lower ones would instead require a joint optimization.

## Expansion

The degrees-of-freedom saving is the point. With a window of 7 loci, a full haplotype test has $2^7-1=127$ degrees of freedom, while a bottom-up test of allele frequencies and pairwise LD has $7+\binom72=28$. Top-down tests act like interaction tests without adjustment for main effects, since a difference in allele frequencies alone can induce an apparent higher-order difference, so they are read as global tests. Higher-order estimates inherit the error of the lower-order ones; in the simulations bottom-up tests had more power than top-down tests, and the single-order bottom-up test ($P=\{1\}$) had the lowest genomic inflation factor in the genome-wide analysis.

## Depends on

- [Joint-cumulant reparametrization of haplotype frequencies](joint-cumulant-reparametrization-of-haplotype-frequencies.md)

## Sources

- B. Balliu, J. J. Houwing-Duistermaat, S. Böhringer, "Powerful testing via hierarchical linkage disequilibrium in haplotype association studies", *Biometrical Journal* (2019), Equations (1) and (4) and section "Testing" (Full, Bottom-Up and Top-Down hypotheses), section "Basic notation and assumptions", and Discussion, <https://doi.org/10.1002/bimj.201800053>, PMCID PMC6637384.
