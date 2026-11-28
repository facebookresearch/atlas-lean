# Variance of genome-wide IBD sharing between full siblings

Consider two full siblings with non-inbred parents and crossovers along each chromosome following the Haldane model (recombination fraction $r(d) = \tfrac12(1 - e^{-2d})$ at map distance $d$ Morgans). At a locus, let $\delta^{(p)}$ ($\delta^{(m)}$) be $1$ if the sibs received the same paternal (maternal) allele, and let the IBD proportion be $\pi = \tfrac12(\delta^{(p)} + \delta^{(m)})$; $\mathbb E\pi = \tfrac12$ and $\operatorname{Var}\pi = \tfrac18$. For loci at distance $d$,

$$\operatorname{Cov}(\delta_i, \delta_j) = \tfrac14 (1 - 2r)^2 = \tfrac14 e^{-4d}.$$

Let $\pi_l$ be the average of $\pi$ over a chromosome of length $l$ Morgans. Then

$$\operatorname{Var}(\pi_l) = \frac{1}{16\, l} - \frac{1 - e^{-4l}}{64\, l^2} = \frac{1}{16\, l} - \frac{r_{2l}}{32\, l^2},$$

where $r_{2l} = r(2l)$. For the genome-wide average $\pi_g = L^{-1}\sum_i l_i \pi_i$ over 22 independent autosomes of total length $L = \sum_i l_i$, using $r_{2l_i} \approx \tfrac12$,

$$\operatorname{Var}(\pi_g) = \frac{1}{L^2}\sum_i l_i^2 \operatorname{Var}(\pi_{l_i}) \approx \frac{1}{16 L} - \frac{22}{64 L^2},$$

so to first order the variance depends only on total map length; for $L = 35$ Morgans, $\operatorname{SD}(\pi_g) \approx 0.039$, versus $\operatorname{SD}(\pi) \approx 0.354$ at one locus.

For IBD2 sharing (both alleles IBD; mean $\tfrac14$, single-locus variance $\tfrac3{16}$), $P(\text{IBD2 at } j \mid \text{IBD2 at } i) = [(1-r)^2 + r^2]^2$, giving $\operatorname{Cov} = \tfrac1{16}(2e^{-4d} + e^{-8d})$. The genome-wide variance of mean IBD2 sharing is about $\tfrac{5}{64L}$ to first order, roughly 30% larger than that of $\pi_g$ when $L = 35$, and the correlation between genome-wide IBD and IBD2 sharing is the ratio of their standard deviations, about $0.89$.

## Expansion

Given that the sibs share the transmitted grandparental allele at locus $i$, they share it at locus $j$ exactly when both meioses recombine or neither does, with probability $(1-r)^2 + r^2$; subtracting $\tfrac14$ gives the covariance, and Haldane's map gives $1 - 2r = e^{-2d}$. Averaging $\tfrac14 e^{-4|x-y|}$ over $[0,l]^2$ gives $\tfrac{1}{8l} - \tfrac{1 - e^{-4l}}{32 l^2}$ for one parent, and the two parents are independent, which halves it for $\pi_l$. The IBD2 case squares the one-parent probability because the two parental transmissions are independent.

## Sources

- P. M. Visscher, S. E. Medland, M. A. R. Ferreira et al., *Assumption-free estimation of heritability from genome-wide identity-by-descent sharing between full siblings*, PLoS Genet. 2 (2006), e41, <https://doi.org/10.1371/journal.pgen.0020041>, PMCID PMC1413498, Materials and Methods, "Variance of genome-wide IBD sharing" (additive and dominance subsections; numerical values $L = 35$, SD $\approx 0.039$, 30% larger IBD2 variance, correlation $0.89$ as stated in the text). The closed forms are rederived above from the covariances stated there.
