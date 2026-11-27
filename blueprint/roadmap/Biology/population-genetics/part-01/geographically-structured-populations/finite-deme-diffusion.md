# Diffusion approximation for a population of finitely many demes

Consider demes $i$ of sizes $N_i$, each reproducing by neutral Wright–Fisher sampling in discrete generations, with a proportion $m_{ij}$ of the individuals of deme $i$ migrating to deme $j$, and the scaling $N_i = O(N)$, $m_{ij} = O(1/N)$ with time measured in units of $N$ generations; Notohara (1990, abstract) proves that the diffusion of the stepping-stone model with migration among colonies, a model of this kind, is dual to the structured coalescent. The forward-in-time diffusion for the allele frequencies follows from the one-generation moments. Let deme $i$ hold $M_i = \kappa_iM$ gene copies, with $M$ a reference number of gene copies per deme; the derivation and the generator below measure time in units of $M$ generations, not $N$, and let $p_{ij}$ be the backward migration matrix: the fraction of the genes of deme $i$ after migration that came from deme $j$, with $\sum_jp_{ij} = 1$ and $p_{ij} = q_{ij}/M$ for $j \ne i$. If migration precedes sampling, the new frequency is $x_i' = Y_i/M_i$ with $Y_i \sim \mathrm{Binomial}(M_i, y_i)$, $y_i = \sum_jp_{ij}x_j$, independently over demes, so

$$E[x_i' - x_i \mid x] = \sum_{j \ne i}\frac{q_{ij}}{M}(x_j - x_i), \qquad \mathrm{Cov}(x_i', x_j' \mid x) = \delta_{ij}\frac{y_i(1 - y_i)}{\kappa_iM}.$$

In time units of $M$ generations, adding local selection and mutation drifts $\beta_i(x_i)$ of order $1/M$ per generation, the limiting generator is

$$Lf = \sum_i\frac{x_i(1 - x_i)}{2\kappa_i}\partial_i^2f + \sum_i\Bigl[\sum_{j \ne i}q_{ij}(x_j - x_i) + \beta_i(x_i)\Bigr]\partial_if,$$

with no cross second-order terms, because the demes resample independently. If sampling precedes migration, $x' = Px''$ with independent binomial $x''$: the mean is the same and the covariance $\sum_kp_{ik}p_{jk}x_k(1 - x_k)/M_k$ differs from the one above by $O(1/M^2)$, so the order of the two steps does not change the limiting generator. For Wright's island model with genic selection, Cherry and Wakeley (2003, abstract) relate the subdivided population to an idealized panmictic Wright–Fisher population with a larger effective size $N_e$ and a smaller effective selection coefficient $s_e$, the product $N_es_e$ being unaltered by subdivision. With genic selection, the forward equation of this generator for a density of derived mutations has the form of the [multi-population diffusion for the joint allele-frequency density](../../diffusion-theory/poisson-random-field-model/multipopulation-diffusion-with-migration-and-admixture.md).

## Depends on

- [Neutral Wright–Fisher transition matrix](../../wright-fisher-markov-chain/wright-fisher.md)

## Expansion

1. The discrete model: local Wright–Fisher sampling and a backward migration matrix, in either order.
2. The conditional means and covariances of one generation's change and their orders in $M$, $\kappa_i$ and $q_{ij}$.
3. The limiting generator, and the vanishing at leading order of the difference between the two orders of migration and sampling.
4. Convergence of the rescaled chains to the diffusion, as a separate statement.

## Sources

- M. Notohara, The coalescent and the genealogical process in geographically structured population, J. Math. Biol. 29 (1990), 59–75, abstract. <https://doi.org/10.1007/BF00173909>
- J. L. Cherry and J. Wakeley, A diffusion approximation for selection and drift in a subdivided population, Genetics 163 (2003), 421–428, abstract. <https://doi.org/10.1093/genetics/163.1.421>
