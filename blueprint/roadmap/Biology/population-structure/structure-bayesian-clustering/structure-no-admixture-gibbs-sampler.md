# STRUCTURE no-admixture model and its Gibbs sampler

**Model.** Let $N$ diploid individuals be genotyped at $L$ unlinked loci, locus $l$ having alleles $\{1, \dots, J_l\}$, and write $x_l^{(i,a)}$, $a \in \{1, 2\}$, for the two allele copies of individual $i$ at locus $l$. Fix $K \ge 1$. Each individual has an unobserved population label $z^{(i)} \in \{1, \dots, K\}$ and population $k$ has allele frequencies $p_{kl\cdot} = (p_{kl1}, \dots, p_{klJ_l})$ in the simplex. Conditionally on $Z = (z^{(i)})$ and $P = (p_{klj})$ the allele copies are independent with

$$\Pr\bigl(x_l^{(i,a)} = j \mid Z, P\bigr) = p_{z^{(i)} l j},$$

i.e. Hardy–Weinberg proportions within populations and linkage equilibrium between loci. The priors are $\Pr(z^{(i)} = k) = 1/K$ independently over $i$, and $p_{kl\cdot} \sim \mathrm{Dirichlet}(\lambda_1, \dots, \lambda_{J_l})$ independently over $(k, l)$, with all $\lambda_j > 0$.

**Full conditionals.** Let $n_{klj} = \#\{(i, a) : z^{(i)} = k,\ x_l^{(i,a)} = j\}$ be the number of copies of allele $j$ at locus $l$ among individuals currently assigned to population $k$. Then

1. given $(X, Z)$, the vectors $p_{kl\cdot}$ are independent with

$$p_{kl\cdot} \mid X, Z \sim \mathrm{Dirichlet}(\lambda_1 + n_{kl1}, \dots, \lambda_{J_l} + n_{klJ_l});$$

2. given $(X, P)$, the labels $z^{(i)}$ are independent with

$$\Pr\bigl(z^{(i)} = k \mid X, P\bigr) = \frac{\prod_{l=1}^{L} \prod_{a=1}^{2} p_{k l x_l^{(i,a)}}}{\sum_{k'=1}^{K} \prod_{l=1}^{L} \prod_{a=1}^{2} p_{k' l x_l^{(i,a)}}}.$$

Alternating these two draws is a Gibbs sampler whose stationary law is the posterior $\Pr(Z, P \mid X)$.

## Expansion

The joint density factorizes as $\prod_i \tfrac1K \prod_{l,a} p_{z^{(i)} l x_l^{(i,a)}} \times \prod_{k,l} \mathrm{Dir}(p_{kl\cdot}; \lambda)$. Collecting the factors that involve one $p_{kl\cdot}$ gives $\prod_j p_{klj}^{\lambda_j - 1 + n_{klj}}$, a Dirichlet kernel (Dirichlet–multinomial conjugacy). Collecting the factors involving one $z^{(i)}$ gives the displayed likelihood ratio, since the uniform prior cancels. Both conditionals factor over $(k, l)$ and over $i$, giving the stated independence.

## Depends on

- [Hardy–Weinberg proportions](../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Proof depends on

- [Dirichlet–multinomial conjugacy](../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/with-density-prod-pow-dirichlet-measure.md)

## Sources

- J. K. Pritchard, M. Stephens and P. Donnelly, "Inference of population structure using multilocus genotype data", *Genetics* 155 (2000), 945–959, <https://doi.org/10.1093/genetics/155.2.945> (PMC1461096).
