# Gamma peak-height likelihood for mixed DNA traces

**Genotype model.** At a short tandem repeat (STR) marker with allelic types $1,\dots,A$, let $n_{ia}\in\{0,1,2\}$ be the number of alleles of type $a$ carried by contributor $i$, with $\sum_an_{ia}=2$. Unknown contributors are unrelated and drawn from a population in Hardy–Weinberg equilibrium with allele frequencies $q_1,\dots,q_A$, so $(n_{i1},\dots,n_{iA})$ is multinomial with 2 trials and probabilities $q$. Markers are independent.

**Peak heights.** Given the genotypes of the $k$ contributors, the peak height at allele $a$ in the electropherogram is $H_a\sim\Gamma(\lambda_a,\eta)$ (shape $\lambda_a$, scale $\eta$), independently over $a$, with

$$
\lambda_a=\rho\sum_{i=1}^k\big\{(1-\xi)n_{ia}+\xi\,n_{i,a+1}\big\}\phi_i,\qquad n_{i,A+1}=0,
$$

where $\phi_i$ is the DNA fraction of contributor $i$, $\xi$ the mean stutter fraction (allele $a+1$ losing one repeat unit and contributing to position $a$), $\rho$ an amplification and variability parameter, and $\Gamma(0,\eta)$ the point mass at $0$. Peaks below a detection threshold $C$ drop out, so the observation is $Z_a=H_a\mathbf 1\{H_a\ge C\}$. The likelihood of $\psi=(\rho,\eta,\xi,\phi)$ is

$$
\ell(\psi)=\prod_{m=1}^ME\Big[\prod_{a=1}^{A_m}f_\psi\big(z_a^m\mid\mathbf n_a,\mathbf n_{a+1}\big)\Big],
$$

where $f_\psi(z\mid\cdot)$ is the gamma density at $z\ge C$ and the probability $P(H_a<C)$ for an unobserved peak, and the expectation runs over the genotypes of unknown contributors. Direct summation has $\{A_m(A_m+1)/2\}^k$ terms per marker.

**Sequential binomial representation.** Let $S_{ia}=\sum_{b\le a}n_{ib}$. Then $S_{i1}=n_{i1}\sim\mathrm{Bin}(2,q_1)$ and, for $a\ge2$,

$$
S_{ia}=S_{i,a-1}+n_{ia},\qquad n_{ia}\mid S_{i,a-1}\sim\mathrm{Bin}\Big(2-S_{i,a-1},\ \frac{q_a}{\sum_{b=a}^Aq_b}\Big),
$$

with $n_{ia}$ conditionally independent of $(n_{i1},\dots,n_{i,a-1},S_{i1},\dots,S_{i,a-2})$ given $S_{i,a-1}$, and $S_{ia}$ conditionally independent of the same variables given $(S_{i,a-1},n_{ia})$. The genotype is therefore a chain-structured Bayesian network. Each peak-height factor depends only on the allele counts $\mathbf n_a,\mathbf n_{a+1}$ at two adjacent types, so the likelihood is an expectation of a factorized function over this network.

## Depends on

- [Expectations of factorized functions as evidence probabilities in a Bayesian network](expectations-of-factorized-functions-as-evidence-probabilities-in-a-bayesian-network.md)
- [Hardy–Weinberg proportions](../../../../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Expansion

Allocating a genotype's two alleles sequentially over types $1,2,\dots$, the number of type-$a$ alleles depends on the past only through how many alleles remain, $2-S_{i,a-1}$. Each remaining allele is type $a$ with probability $q_a/\sum_{b\ge a}q_b$ given that it is not of a smaller type, which is the stated binomial. The ratio of multinomial probabilities collapses to exactly this binomial. Attaching one auxiliary evidence node per factor $f_\psi(z_a\mid\mathbf n_a,\mathbf n_{a+1})$ turns $\ell(\psi)$ into a ratio of normalizing constants computed by a single propagation, and the same propagation gives posterior genotype probabilities for the unknown contributors. The gamma family enters only through how $\lambda_a$ depends on the counts at $a$ and $a+1$, so other peak-height laws with this locality can be substituted.

## Sources

- T. Graversen, S. Lauritzen, "Computational aspects of DNA mixture analysis", *Statistics and Computing* 25 (2015), 527–541, <https://doi.org/10.1007/s11222-014-9451-7>; preprint arXiv:1307.4956 (2013), Section 2 (genotype model, gamma peak-height model (1) and likelihood (2)) and Section 3.2 (Bayesian network representation of genotypes, Proposition 3), <https://doi.org/10.48550/arXiv.1307.4956>.
