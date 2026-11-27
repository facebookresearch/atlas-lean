# Equivalence test of Hardy-Weinberg equilibrium for X-chromosomal SNPs

**Setting.** At a diallelic X-chromosomal locus with alleles $A$ and $a$, females carry genotypes $AA, Aa, aa$ with probabilities $(\pi_1,\pi_2,\pi_3)$ and males carry allele $A$ with probability $p_Y$. Hardy-Weinberg equilibrium (HWE) on the X chromosome requires both $\pi_2^2=4\pi_1\pi_3$ in females and equal allele frequencies in the sexes, $p_1:=\pi_1+\pi_2/2=p_Y$. Define the signed disequilibrium components

$$\Delta_f^{\pm}=\log\pi_2-\tfrac12(\log\pi_1+\log\pi_3)-\log 2,\qquad
\Delta_m^{\pm}=\operatorname{logit}(p_1)-\operatorname{logit}(p_Y),$$

the log relative excess heterozygosity in females and the log odds ratio of $A$ between the sexes, and the aggregate distance $\Delta=\big((\Delta_f^{\pm})^2+(\Delta_m^{\pm})^2\big)^{1/2}$. The goodness-of-fit problem is the equivalence problem

$$H_0:\ \Delta\ge\varepsilon\qquad\text{versus}\qquad H_1:\ \Delta<\varepsilon,$$

so that rejecting $H_0$ establishes approximate compatibility with HWE; the proposed margin is $\varepsilon=\sqrt2\log1.4\approx0.48$.

**Proposition 1 (joint asymptotics).** Let $(X_1,X_2,X_3)\sim\mathrm{Mult}(n_1;\pi)$ (females) and $Y\sim\mathrm{Bin}(n_2,p_Y)$ (males) be independent, $N=n_1+n_2$, $n_1/N\to\lambda\in(0,1)$, and let $\hat\Delta_f^{\pm},\hat\Delta_m^{\pm}$ be the plug-in estimators. Then $\sqrt N(\hat\Delta_f^{\pm}-\Delta_f^{\pm},\ \hat\Delta_m^{\pm}-\Delta_m^{\pm})$ converges to a pair of independent centered normals with variances

$$\sigma_f^2=\frac1\lambda\Big(\frac{1-\pi_2}{4\pi_1\pi_3}+\frac1{\pi_2}\Big),\qquad
\sigma_m^2=\frac{\pi_1+\pi_2/4-p_1^2}{\lambda\,p_1^2(1-p_1)^2}+\frac{1}{(1-\lambda)\,p_Y(1-p_Y)} .$$

**Proposition 2 (asymptotic normality of the distance).** If $\Delta>0$, then $\sqrt N(\hat\Delta-\Delta)\to\mathcal N(0,\tau^2)$ with

$$\tau^2=\frac{(\Delta_f^{\pm})^2\sigma_f^2+(\Delta_m^{\pm})^2\sigma_m^2}{(\Delta_f^{\pm})^2+(\Delta_m^{\pm})^2}.$$

Consequently the test rejecting $H_0$ when $\hat\Delta+z_{1-\alpha}\hat\tau/\sqrt N<\varepsilon$ has asymptotic level $\alpha$, and its power at a fixed $\Delta<\varepsilon$ is approximately $\Phi\big(\sqrt N(\varepsilon-\Delta)/\tau-z_{1-\alpha}\big)$.

## Depends on

- [Deviation from Hardy-Weinberg proportions](../hw-deviation.md)
- [Multinomial distribution](../../../../Probability/distributions/discrete/multinomial-distribution/multinomial.md)

## Proof depends on

- [Delta method](../../../../Probability/convergence-of-measures/slutsky-s-theorem-and-the-delta-method/delta-method.md)

## Expansion

Apply the delta method to the multinomial and binomial central limit theorems. With $g=(-\tfrac1{2\pi_1},\tfrac1{\pi_2},-\tfrac1{2\pi_3})$ the gradient of $\Delta_f^{\pm}$ and $h=(1,\tfrac12,0)$ the gradient of $p_1$, the multinomial covariance $\operatorname{diag}(\pi)-\pi\pi^{\top}$ gives $\sum_j g_j^2\pi_j=\sigma_f^2\lambda$ (because $g\cdot\pi=0$) and $\sum_jg_jh_j\pi_j-(g\cdot\pi)(h\cdot\pi)=-\tfrac12+\tfrac12=0$, so the female heterozygosity component is asymptotically uncorrelated with the female allele frequency; the male sample is independent of both. The logit transform contributes the factor $1/(p(1-p))^2$. Proposition 2 is the delta method for $(u,v)\mapsto\sqrt{u^2+v^2}$ away from the origin. At $\Delta=0$ the limit of $\sqrt N\hat\Delta$ is instead the norm of an anisotropic Gaussian vector, with an explicit distribution function used for small-$\Delta$ calibration.

## Sources

- Wellek S, Ziegler A, "Testing for goodness rather than lack of fit of an X-chromosomal SNP to the Hardy-Weinberg model", PLoS One 14(2):e0212344, Equations (7)-(19) and Propositions 1-3, <https://doi.org/10.1371/journal.pone.0212344>, PMCID PMC6383894.
