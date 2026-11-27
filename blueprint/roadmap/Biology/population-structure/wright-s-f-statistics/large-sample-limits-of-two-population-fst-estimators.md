# Large-sample limits of two-population $F_{ST}$ estimators under population-specific drift

Consider a biallelic SNP with ancestral allele frequency $p \in (0,1)$ and two populations descended from that ancestor. Following Weir and Hill, population $i \in \{1,2\}$ carries a population-specific $F_{ST}$ value $F_i \in [0,1]$, defined by the drift moments

$$\mathbb E[p_i] = p, \qquad \operatorname{Var}(p_i) = p(1-p)\,F_i, \qquad \operatorname{Cov}(p_1, p_2) = 0,$$

where $p_i$ is the present frequency in population $i$. Write $\bar F = (F_1 + F_2)/2$. Let the two sample sizes tend to infinity, so that sample frequencies converge to $p_1, p_2$, and replace every numerator and denominator by its expectation over drift (the quantity estimated when many independent SNPs are combined as a ratio of averages).

1. **Hudson.** With numerator $N_H = (p_1 - p_2)^2$ and denominator $D_H = p_1(1-p_2) + p_2(1-p_1)$,

$$\frac{\mathbb E[N_H]}{\mathbb E[D_H]} = \frac{2p(1-p)\bar F}{2p(1-p)} = \bar F .$$

The Hudson estimator targets exactly the average of the population-specific values, does not depend on the sample sizes, and never exceeds $1$.
2. **Nei.** With numerator $(p_1 - p_2)^2$ and denominator $2\tilde p(1-\tilde p)$, where $\tilde p = (p_1+p_2)/2$ is the pooled frequency,

$$\frac{2p(1-p)\bar F}{2p(1-p)\,(1 - \bar F/2)} = \frac{\bar F}{1 - \bar F/2} \;\ge\; \bar F,$$

with equality only when $\bar F = 0$; the limit rises to $2$ as $F_1, F_2 \to 1$. Nei's estimator therefore systematically overestimates the average population-specific $F_{ST}$.
3. **Weir–Cockerham.** The sample-size-weighted Weir–Cockerham estimator, designed for $F_1 = F_2$, converges to a value that depends on the limiting ratio $M$ of the two sample sizes whenever $F_1 \ne F_2$; when $F_1 = F_2 = F$ the dependence on $M$ disappears and the limit is $F$.

## Depends on

- [Hudson's $F_{ST}$ (ratio of averages)](../abba-baba-test-and-f-statistic-estimators/hudson-fst.md)
- [Weir–Cockerham estimator of $\theta$ (moment estimator of $F_{ST}$)](weir-cockerham-theta-estimator.md)

## Expansion

Independence and unbiasedness of drift give $\mathbb E[(p_1-p_2)^2] = \operatorname{Var}(p_1) + \operatorname{Var}(p_2) = 2p(1-p)\bar F$ and $\mathbb E[p_1 p_2] = p^2$, so $\mathbb E[D_H] = 2p - 2p^2$. For Nei's pooled denominator, $\mathbb E[\tilde p^2] = p^2 + p(1-p)\bar F/2$, hence $\mathbb E[2\tilde p(1-\tilde p)] = 2p(1-p)(1 - \bar F/2)$. Both denominators average over the ancestral population in the Hudson case but over the current samples in the Nei case, which is why only the former targets drift relative to the most recent common ancestor. The Hudson estimator is the simple average of the Weir–Hill population-specific estimators. Bhatia et al. record the three limits as Equations 1–3 of their Results and recommend the Hudson estimator for pairs of populations; on 1000 Genomes data, subsampling either CEU or CHB to 14 individuals gave Weir–Cockerham estimates of 0.114 and 0.107 for the same pair of populations, a difference of more than eight standard errors, whereas the two Hudson estimates agreed.

## Sources

- G. Bhatia, N. Patterson, S. Sankararaman, A. L. Price, "Estimating and interpreting $F_{ST}$: the impact of rare variants", Genome Research 23 (2013), 1514–1521, <https://doi.org/10.1101/gr.154831.113> (PMC3759727), Results "Choice of $F_{ST}$ estimator" (Equations 1–3) and Methods.
- B. S. Weir and W. G. Hill, "Estimating F-statistics", Annual Review of Genetics 36 (2002), 721–750, <https://doi.org/10.1146/annurev.genet.36.050802.093940>.
