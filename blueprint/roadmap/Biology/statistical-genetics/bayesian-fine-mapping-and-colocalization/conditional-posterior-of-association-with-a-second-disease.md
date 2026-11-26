# Conditional posterior of association with a second disease

For one SNP and two diseases consider the four hypotheses $H_0$ (associated with neither), $H_1$ (disease 1 only), $H_2$ (disease 2 only) and $H_{12}$ (both), with prior probabilities $\pi_0, \pi_1, \pi_2, \pi_{12} > 0$ summing to $1$. Let $\phi_k > 0$ be the Bayes factor for association versus no association with disease $k$ computed from disease $k$'s data alone (for example, [Wakefield's approximate Bayes factor](wakefield-abf.md) from the SNP's $p$-value and allele frequency). If the two case–control data sets are independent (no shared controls), the Bayes factors of the four hypotheses against $H_0$ are $1, \phi_1, \phi_2, \phi_1 \phi_2$, so

$$\mathrm{PP}_h = \frac{\pi_h\, \mathrm{BF}_h}{\pi_0 + \pi_1 \phi_1 + \pi_2 \phi_2 + \pi_{12} \phi_1 \phi_2}, \qquad h \in \{0, 1, 2, 12\}.$$

**Proposition.** The posterior probability of association with disease 2 given association with disease 1 is

$$\mathrm{PP}_{2 \mid 1} = \frac{\mathrm{PP}_{12}}{\mathrm{PP}_1 + \mathrm{PP}_{12}} = \frac{\pi_{12}\, \phi_2}{\pi_1 + \pi_{12}\, \phi_2},$$

which does not depend on $\phi_1$, is strictly increasing in $\phi_2$, and exceeds a level $\tau \in (0,1)$ iff

$$\phi_2 > \frac{\tau}{1 - \tau} \cdot \frac{\pi_1}{\pi_{12}} .$$

With $\pi_1 = \pi_2 = 10^{-4}$ and $\pi_{12} = 10^{-5}$, convincing evidence $\mathrm{PP}_{2|1} > 0.9$ requires $\phi_2 > 90$, whatever the strength of the disease-1 signal.

## Depends on

- [Wakefield's approximate Bayes factor](wakefield-abf.md)

## Expansion

The normalizing constant cancels in the ratio, and the common factor $\phi_1$ cancels between $\mathrm{PP}_1 \propto \pi_1 \phi_1$ and $\mathrm{PP}_{12} \propto \pi_{12}\phi_1\phi_2$. Monotonicity and the threshold follow by solving $\pi_{12}\phi_2 / (\pi_1 + \pi_{12}\phi_2) > \tau$. The prior ratio $\pi_{12}/\pi_1 = 0.1$ encodes the belief that one in ten SNPs associated with one autoimmune disease is associated with the other. Onengut-Gumuscu et al. used this to show that the earlier rule "$p < 10^{-4}$ for type 1 diabetes at a SNP genome-wide significant in another autoimmune disease" gives $\mathrm{PP}_{2|1}$ well above $0.9$ only with independent controls; when the diseases share controls, $\mathrm{BF}_{12} \ne \phi_1 \phi_2$ and simulation gives a median $\mathrm{PP}_{2|1}$ of about $0.46$ at $p_2 = 10^{-4}$, so they recommend $p_2 < 10^{-5}$.

## Sources

- S. Onengut-Gumuscu, W.-M. Chen, O. Burren et al., "Fine mapping of type 1 diabetes susceptibility loci and evidence for colocalization of causal variants with lymphoid gene enhancers", Nature Genetics 47 (2015), Online Methods "Evidence for T1D association conditional on genome-wide significant association in another autoimmune disease" (hypotheses, priors, $\mathrm{PP}_{2|1}$), <https://doi.org/10.1038/ng.3245>, PMCID PMC4380767.
