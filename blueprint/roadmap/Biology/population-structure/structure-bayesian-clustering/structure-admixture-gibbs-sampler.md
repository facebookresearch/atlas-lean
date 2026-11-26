# STRUCTURE admixture model and its Gibbs sampler

**Model.** With the notation of the [no-admixture model](structure-no-admixture-gibbs-sampler.md), each individual $i$ now has an ancestry vector $q^{(i)} = (q_1^{(i)}, \dots, q_K^{(i)})$ in the simplex, and each allele copy has its own origin $z_l^{(i,a)} \in \{1, \dots, K\}$. Conditionally on $Q = (q^{(i)})$ the origins are independent with $\Pr(z_l^{(i,a)} = k \mid Q) = q_k^{(i)}$, and conditionally on $(Z, P)$ the allele copies are independent with

$$\Pr\bigl(x_l^{(i,a)} = j \mid Z, P, Q\bigr) = p_{z_l^{(i,a)} l j}.$$

Priors: $q^{(i)} \sim \mathrm{Dirichlet}(\alpha, \dots, \alpha)$ independently, $\alpha > 0$, and $p_{kl\cdot} \sim \mathrm{Dirichlet}(\lambda_1, \dots, \lambda_{J_l})$ independently.

**Full conditionals.** Let $n_{klj} = \#\{(i, a) : z_l^{(i,a)} = k,\ x_l^{(i,a)} = j\}$ and $m_k^{(i)} = \#\{(l, a) : z_l^{(i,a)} = k\}$. Then

1. $p_{kl\cdot} \mid X, Z \sim \mathrm{Dirichlet}(\lambda_1 + n_{kl1}, \dots, \lambda_{J_l} + n_{klJ_l})$, independently over $(k, l)$;
2. $q^{(i)} \mid X, Z \sim \mathrm{Dirichlet}(\alpha + m_1^{(i)}, \dots, \alpha + m_K^{(i)})$, independently over $i$;
3. given $(X, P, Q)$ the origins are independent with

$$\Pr\bigl(z_l^{(i,a)} = k \mid X, P, Q\bigr) = \frac{q_k^{(i)}\, p_{k l x_l^{(i,a)}}}{\sum_{k'=1}^{K} q_{k'}^{(i)}\, p_{k' l x_l^{(i,a)}}}.$$

Summing out $Z$, the likelihood of $(P, Q)$ is $\prod_{i,l,a} \sum_k q_k^{(i)} p_{k l x_l^{(i,a)}}$, the [admixture log-likelihood](../admixture-model-and-the-frappe-em-algorithm/admixture-log-lik.md) in exponentiated form for biallelic loci.

## Expansion

As in the no-admixture case, each conditional is read off the joint density: the $p$ and $q$ factors are Dirichlet kernels with counts added to the prior parameters, and each origin $z_l^{(i,a)}$ appears only in the factor $q_{z}^{(i)} p_{z l x}$, which normalizes to step 3. Summing step 3's numerator over $k$ gives the per-copy mixture likelihood.

## Depends on

- [STRUCTURE no-admixture model and its Gibbs sampler](structure-no-admixture-gibbs-sampler.md)
- [Admixture log-likelihood](../admixture-model-and-the-frappe-em-algorithm/admixture-log-lik.md)

## Proof depends on

- [Dirichlet–multinomial conjugacy](../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/with-density-prod-pow-dirichlet-measure.md)
- [STRUCTURE no-admixture model and its Gibbs sampler](structure-no-admixture-gibbs-sampler.md)

## Sources

- J. K. Pritchard, M. Stephens and P. Donnelly, "Inference of population structure using multilocus genotype data", *Genetics* 155 (2000), 945–959, <https://doi.org/10.1093/genetics/155.2.945> (PMC1461096). The admixture model and its Gibbs algorithm; no equation numbers are cited because only the abstract was available.
