# Asymptotic normality of within-family residuals under dominance

Consider a diploid population whose trait is determined by $M$ unlinked loci. The founders of the pedigree are unrelated and drawn from an ancestral population in linkage equilibrium and Hardy–Weinberg equilibrium. At locus $l$ an individual carries allelic states $\chi_l^1,\chi_l^2$, and the genetic component of its trait is

$$
Z=\bar z_0+\frac{1}{\sqrt M}\sum_{l=1}^M\Big(\eta_l(\chi_l^1)+\eta_l(\chi_l^2)+\phi_l(\chi_l^1,\chi_l^2)\Big),
$$

where the additive effects $\eta_l$ and the symmetric dominance effects $\phi_l$ take values in a fixed interval $[-B,B]$ and are normalized in the ancestral population ($\mathbb E[\eta_l(\hat\chi_l)]=0$, $\mathbb E[\phi_l(\hat\chi_l,x')]=0$ for every allele $x'$). Assume that the scaled inbreeding depression

$$
\iota=\frac{1}{\sqrt M}\sum_{l=1}^M\mathbb E[\phi_l(\hat\chi_l,\hat\chi_l)]
$$

stays bounded as $M\to\infty$, with $\hat\chi_l$ an ancestral allele at locus $l$. The observed trait is $\widetilde Z^i=Z^i+E^i$, where the environmental noise $E^i$ is Gaussian, $E^i\sim N(0,\sigma_E^2)$ with $\sigma_E^2>0$, independent of the genetic components, and shared by all offspring of a family (so it is part of the family-shared component, and the observed traits have a smooth density). Write the genetic value of offspring $i$ with parents $i[1],i[2]$ as $Z^i=(\mathcal A^i+\mathcal D^i)+(R_A^i+R_D^i)$, a part shared by the whole family plus Mendelian residuals from the additive and dominance components.

Assume the residual variance $\operatorname{Var}(R_A^i+R_D^i)$, computed conditional on $\mathcal P(t-1)$, is positive. Then, conditional on the pedigree up to generation $t$, $\mathcal P(t)$, and on the observed parental traits $\widetilde Z^{i[1]},\widetilde Z^{i[2]}$, the standardized residual $(R_A^i+R_D^i)/\sqrt{\operatorname{Var}(R_A^i+R_D^i)}$ is standard normal up to an error of order $1/\sqrt M$: for every $z\in\mathbb R$ the difference between its conditional distribution function and $\Phi(z)$ is at most

$$
\frac{1}{\sqrt M}\,\frac{C'}{\sqrt{\operatorname{Var}(R_A^i+R_D^i)}}\Big(1+\frac{\widetilde C'}{\operatorname{Var}(R_A^i+R_D^i)}\Big)\big(1+\mathfrak C(i[1],i[2])\big),
$$

where the constants $C',\widetilde C'$ depend only on the bound $B$, and $\mathfrak C$ grows with the standardized deviations of the parental traits from their conditional means and with the reciprocal of the normal density at those deviations. So the limit holds unless the parents' traits are extreme relative to the population.

## Depends on

- [Infinitesimal model definition](../../mendelian-segregation-and-the-infinitesimal-mode/infinitesimal-model-definition.md)

## Expansion

Conditionally on which parental gene is passed at each locus, the residual is a sum of $M$ bounded, weakly dependent terms of size $1/\sqrt M$. A Berry–Esseen bound for sums with a dependency graph (Rinott's bound) gives the $1/\sqrt M$ rate. The extra work is to show that conditioning on the parents' observed traits barely distorts the allele distribution at any single locus; this costs the factor $\mathfrak C$, which is large only when a parental trait sits in the far tail. The bounded $\iota$ keeps inbreeding depression finite. Without it the dominance part would not have an order-one limit.

## Sources

- Nicholas H. Barton, Alison M. Etheridge and Amandine Véber, "The infinitesimal model with dominance", *Genetics* 225 (2023), iyad133, <https://doi.org/10.1093/genetics/iyad133>. Numbering as in the preprint arXiv:2211.03515v3, <https://arxiv.org/abs/2211.03515v3>: Section 3 (model and the definition of $\iota$), Section 5 (Mendelian model, and the paragraph "Main results" on the Gaussian shared environmental noise) and Theorem 5.1 with Eqs. (30)–(31).
