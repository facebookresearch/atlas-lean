# Individual-specific allele-frequency score test for Hardy–Weinberg equilibrium

Let $n$ individuals be typed at a biallelic site, with genotype likelihoods $L_i(G)=\Pr(\mathrm{Data}_i\mid g_i=G)$ for $G\in\{0,1,2\}$, and genetic-ancestry coordinates $x_i\in\mathbb R^k$ (for example principal components). Model the nonreference allele frequency of individual $i$ as the clipped linear function

$$p_i=p(x_i;\beta)=\min\big(1-\varepsilon,\ \max(\varepsilon,\ \beta^\top x_i)\big),\qquad q_i=1-p_i,$$

with a small floor $\varepsilon>0$. Under the alternative with inbreeding coefficient $\theta$ the genotype frequencies of $(0,1,2)$ are $\big(q_i^2+\theta p_iq_i,\ 2p_iq_i(1-\theta),\ p_i^2+\theta p_iq_i\big)$, and $\theta=0$ is Hardy–Weinberg equilibrium with individual-specific frequencies. The log-likelihood is

$$\ell(\beta,\theta)=\sum_{i=1}^n\log\Big(L_i(0)\big(q_i^2+\theta p_iq_i\big)+L_i(1)\,2p_iq_i(1-\theta)+L_i(2)\big(p_i^2+\theta p_iq_i\big)\Big).$$

Its score in $\theta$ is $U(\theta)=\sum_iu_i(\theta)$ with

$$u_i(\theta)=\frac{p_iq_i\big(L_i(0)-2L_i(1)+L_i(2)\big)}{L_i(0)(q_i^2+\theta p_iq_i)+L_i(1)\,2p_iq_i(1-\theta)+L_i(2)(p_i^2+\theta p_iq_i)},$$

and since $u_i'(\theta)=-u_i(\theta)^2$ the observed information at $\theta=0$ is $\sum_iu_i(0)^2$. With $\beta$ estimated under the null by EM, the score statistic

$$T_{\mathrm{score}}=\frac{\big(\sum_iu_i(0)\big)^2}{\sum_iu_i(0)^2}$$

is asymptotically $\chi^2_1$ under $H_0:\theta=0$. The likelihood-ratio statistic $2\big[\max_{\beta,\theta}\ell-\max_\beta\ell(\beta,0)\big]$ has the same limit.

## Depends on

- [Hardy–Weinberg genotype proportions](../../association-tests/testing-hardy-weinberg-equilibrium/hwe-prob.md)

## Expansion

Each likelihood term is linear in $\theta$, so $u_i=a_i/(b_i+c_i\theta)$ with $c_i=a_i$, and differentiating gives $-u_i^2$. A single shared frequency in a structured or admixed sample produces a spurious heterozygote deficit (the Wahlund effect); letting the frequency vary with ancestry removes it, while genotype likelihoods keep low-depth uncertainty from masquerading as departure from equilibrium. For hard-called array genotypes with per-allele error $e_i$, the likelihoods $(1-e_i)^2$, $2e_i(1-e_i)$, $e_i^2$ are used. With discrete subpopulations, the stratified alternative is to meta-analyse per-group $z$-scores by Stouffer's method, $T_{\mathrm{meta}}=\sum_iz_i\sqrt{n_i}\big/\sqrt{\sum_in_i}$.

## Sources

- A. M. Kwong et al., "Robust, flexible, and scalable tests for Hardy–Weinberg equilibrium across diverse ancestries", Genetics 218 (2021), iyab044, Materials and methods (sections on RUTH, the score test and the likelihood ratio test), <https://doi.org/10.1093/genetics/iyab044>, PMCID PMC8128395.
