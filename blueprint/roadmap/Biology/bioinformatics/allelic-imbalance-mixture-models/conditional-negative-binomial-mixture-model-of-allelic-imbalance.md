# Conditional negative binomial mixture model of allelic imbalance

**Data.** For SNVs $i=1,\dots,N$ observed in a sequencing assay (ChIP-seq, ATAC-seq, DNase-seq, RNA-seq, ...), let $x_i,y_i$ be the reference and alternative read counts. Copy-number context is summarized by the *background allelic dosage* $\mathrm{BAD}$ (ratio of major to minor allele copies), giving $p=\mathrm{BAD}/(\mathrm{BAD}+1)$; $\mathrm{BAD}=1$ means $p=1/2$.

**Model family.** One allele count is modeled conditionally on the other. With reference-bias line $r(x;b,a)=bx+a$ and left truncation at a coverage threshold $l$ (to discard SNP-calling noise), $f_l(y)=g(y)\mathbf 1_{y\ge l}/(1-G(l))$ for a base law $g$ with distribution function $G$:

1. *Negative binomial:* $y\mid x\sim\mathrm{NB}(r(x;b_x,a_x),p)$ truncated at $l$.
2. *Beta negative binomial* (extra overdispersion): $p\sim\mathrm{Beta}(\mu\kappa,(1-\mu)\kappa)$ integrated out; $\kappa\to\infty$ recovers model 1.
3. *Marginalized compound negative binomial* (error in the conditioning count): $y\sim\mathrm{NB}(\hat x,p)$ with $\hat x\sim$ zero-truncated $\mathrm{Bin}(r,1-p)$, whose marginal is

$$
f_{\mathrm{MCNB}}(y\mid r,p)=\frac{r(1-p)^2p^{r+y-1}\,{}_2F_1\!\big(1-r,\,y+1;\,2;\,-\tfrac{(1-p)^2}{p}\big)}{1-p^r}.
$$

**Mixture over parental chromosomes.** Since phasing is unknown, each SNV's reads come from one parental copy with weight $w$:

$$
f_{\mathrm{Mix}}(y\mid p,\theta)=w\,f(y\mid p,\theta)+(1-w)\,f(y\mid 1-p,\theta),
$$

where $f$ is any of the three laws. The size parameter is rescaled so means match the NB interpretation: $r_{\mathrm{MCNB}}=r\,\frac{1-p^r}{1-p}$ and $r_{\mathrm{BetaNB}}=r\,\frac{(1-\mu)\kappa-1}{(1-\mu)\kappa}$.

**Estimation and scoring.** Parameters are fitted by maximum likelihood, separately for $y\mid x$ and $x\mid y$, in sliding windows over the conditioning count; BetaNB optionally uses a MAP penalty from $1/\kappa\sim\mathrm{Exp}$ with scale growing with the window. Each SNV gets right-tailed $p$-values $\Pr(Y\ge y\mid x)$ and $\Pr(X\ge x\mid y)$; replicate $p$-values are combined by the logit method, and the smaller of the two allele-wise combined $p$-values (with its effect size) is reported.

## Depends on

- [Negative binomial laws of allelic read counts](negative-binomial-laws-of-allelic-read-counts.md)

## Expansion

The conditional formulation avoids modeling the joint law of $(x,y)$ and directly yields a null distribution for one allele given the other, which is what an imbalance test needs. The linear size $r=bx+a$ follows from binomial thinning of an NB total (where $b=1$, $a=r_0$) and lets $b\neq1$ absorb reference mapping bias. BAD mixtures handle aneuploid and CNV regions without phasing, because a copy-number imbalance shifts $p$ in an unknown direction. The three base laws trade sensitivity for specificity: BetaNB has heavy tails and gives conservative $p$-values at small $\kappa$, while MCNB treats the conditioning count as noisy.

## Sources

- Georgy Meshcheryakov, Sergey Abramov, Aleksandr Boytsov, Andrey I. Buyan, Vsevolod J. Makeev, Ivan V. Kulakovskiy, "MIXALIME: MIXture models for ALlelic IMbalance Estimation in high-throughput sequencing data", arXiv:2306.08287 (2023), sections on the negative binomial, beta negative binomial, marginalized compound negative binomial and mixture models, reparametrization of $r$, parameter estimation and scoring of individual SNVs, <https://doi.org/10.48550/arXiv.2306.08287>.
