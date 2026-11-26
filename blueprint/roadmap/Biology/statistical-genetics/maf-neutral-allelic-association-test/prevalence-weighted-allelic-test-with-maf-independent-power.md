# Prevalence-weighted allelic test with MAF-independent power

**Setting.** A biallelic marker with alleles $M_1, M_2$ is tested for association with a disease in a case–control sample of $R$ cases and $S$ controls ($N = R + S$, case fraction $\lambda = R/N$), under Hardy–Weinberg equilibrium at the marker. Let $q_i^A$, $q_i^U$ and $q_i$ be the frequencies of $M_i$ among cases, controls and in the population, and let $\pi$ be the disease prevalence, so $q_i = \pi q_i^A + (1-\pi)q_i^U$. A causal biallelic variant with alleles $A_1, A_2$ has frequencies $p_i$, $p_i^A$, $p_i^U$, and the marker–variant linkage disequilibrium is $\Delta = D_{11}/\sqrt{p_1p_2q_1q_2}$ with $D_{11} = \mathbb{P}(A_1M_1) - p_1q_1$.

**Statistic.** With sample frequencies $\hat q_i^A, \hat q_i^U$, an external consistent prevalence estimate $\hat\pi$, $\hat q_{i,\hat\pi} = \hat\pi\hat q_i^A + (1-\hat\pi)\hat q_i^U$ and $m = 2N\lambda(1-\lambda)$, define
$$W_{\hat\pi} = \frac{\sqrt{m}\,(\hat q_1^U - \hat q_1^A)}{\sqrt{\hat q_{1,\hat\pi}\,\hat q_{2,\hat\pi}}},$$
compared with the usual allelic statistic $T$, whose denominator is $\sqrt{\lambda\hat q_1^U\hat q_2^U + (1-\lambda)\hat q_1^A\hat q_2^A}$.

**Proposition.**
1. *Null law.* Under no association, $W_{\hat\pi} \to \mathcal{N}(0,1)$ in distribution.
2. *LD identity.* With a single causal variant, $\dfrac{q_1^U - q_1^A}{\sqrt{q_1q_2}} = \Delta\,\dfrac{p_1^U - p_1^A}{\sqrt{p_1p_2}}$.
3. *Asymptotic power.* With $B = (p_1^U - p_1^A)/\sqrt{p_1p_2}$ (a property of the causal variant only) and $Q^2 = \dfrac{q_1q_2}{\lambda q_1^Uq_2^U + (1-\lambda)q_1^Aq_2^A}$,
$$W_{\hat\pi} = \sqrt{m}\,\Delta B + O_P(1), \qquad T = \sqrt{m}\,\Delta B\,Q + O_P(1).$$
So the power of $W_{\hat\pi}$ depends on the marker only through $\Delta$, whereas $T$ is reweighted by the marker's allele frequencies through $Q$; both have the same level since $Q = 1$ under the null. If $M_1$ is enriched in cases and $q_1^A < \frac12$, then $Q \le 1$ (so $W_{\hat\pi}$ is more powerful) exactly when $\lambda \le \lambda_0 = \dfrac{q_1^Aq_2^A - q_1q_2}{q_1^Aq_2^A - q_1^Uq_2^U}$.
4. *Relation to the trend test.* Under the additive model, $W_{\hat\pi}^2 = T_{\mathrm{CATT}}^2(1/2)\,\dfrac{q_{1,p}q_{2,p}}{q_{1,\pi}q_{2,\pi}} + o_P(1)$ with pooled frequencies $q_{i,p}$, so $W_{\hat\pi}$ and the Cochran–Armitage trend test (equivalently the logistic-regression score test) share the asymptotic level and differ in power by the ratio of pooled to population heterozygosity.

## Expansion

Case–control sampling oversamples cases, so pooled allele frequencies are biased toward the case frequencies; standardizing by the population frequencies reconstructed with the prevalence removes the extra weight that standard tests put on markers with high minor allele frequency. The LD identity follows by conditioning marker alleles on the causal genotype: the marker frequency difference between cases and controls is the causal difference transmitted through $D_{11}$. Hence, at fixed sample size, the noncentrality of $W_{\hat\pi}$ is $\sqrt{m}\Delta B$, flat in the marker MAF, which makes $p$-values comparable across rare and common markers in LD with the same variant. Robustness to misspecifying $\pi$ is good for rare diseases, and adjusted versions handle Hardy–Weinberg disequilibrium.

## Sources

- M. A. Jonker and J. Pecanka, "A powerful MAF-neutral allele-based test for case-control association studies", arXiv:2002.05048 (2020), Sections 2.1–2.3 (statistic, the LD identity derived in Appendix A, and asymptotic power comparisons with the allelic test and the Cochran–Armitage trend test), Lemmas 4.1 and 4.2 (appendix), <https://doi.org/10.48550/arXiv.2002.05048>.
