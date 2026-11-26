# Negative binomial laws of allelic read counts

**Setting.** At a heterozygous single-nucleotide variant, let $x$ and $y$ be the read counts supporting the two alleles and $n=x+y$ the total coverage. Write $\mathrm{NB}(r,p)$ for the negative binomial law with probability mass $\binom{k+r-1}{k}p^k(1-p)^r$, $k\ge0$ (mean $rp/(1-p)$).

**Theorem.** Suppose that, given the total, reads are assigned to alleles independently, and the total is overdispersed:

$$
x\mid n\sim\mathrm{Bin}(n,p),\qquad y\mid n\sim\mathrm{Bin}(n,1-p),\qquad n\sim\mathrm{NB}(r_0,p_0).
$$

Then:

1. *(Marginals.)*

$$
x\sim\mathrm{NB}\Big(r_0,\ \frac{p_0p}{1-(1-p)p_0}\Big),\qquad y\sim\mathrm{NB}\Big(r_0,\ \frac{p_0(1-p)}{1-pp_0}\Big).
$$

2. *(Conditionals.)*

$$
y\mid x\sim\mathrm{NB}\big(x+r_0,\ p_0(1-p)\big),\qquad x\mid y\sim\mathrm{NB}\big(y+r_0,\ p_0p\big).
$$

In particular, the count at one allele given the count at the other is negative binomial with a size parameter that is affine in the observed count, $r=x+r_0$.

## Expansion

The marginal follows from probability generating functions: $\mathbb E s^n=\big((1-p_0)/(1-p_0s)\big)^{r_0}$, and binomial thinning substitutes $s\mapsto1-p+ps$, which returns a negative binomial generating function with success parameter $q=p_0p/(1-p_0(1-p))$. For the conditional, the joint mass is $\Pr(x,y)=\Pr(n=x+y)\binom{x+y}{x}p^x(1-p)^y$; dividing by the marginal of $x$ and collecting the $y$-dependent factors gives $\binom{x+r_0+y-1}{y}\,(p_0(1-p))^y$ times a normalizing constant, i.e. $\mathrm{NB}(x+r_0,p_0(1-p))$. This is the generative justification for modeling allelic imbalance with a negative binomial whose size depends linearly on the other allele's count: the slope absorbs reference-mapping bias, and departures of $p$ from $1/2$ signal allele-specific expression or binding.

## Sources

- Georgy Meshcheryakov, Sergey Abramov, Aleksandr Boytsov, Andrey I. Buyan, Vsevolod J. Makeev, Ivan V. Kulakovskiy, "MIXALIME: MIXture models for ALlelic IMbalance Estimation in high-throughput sequencing data", arXiv:2306.08287 (2023), appendix "On the origins of NB distribution in allelic read counting" (link lemma, theorems on marginals and conditional distributions), <https://doi.org/10.48550/arXiv.2306.08287>.
