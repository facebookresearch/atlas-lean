# Power posterior for Poisson NMF

**Model.** Let $X = (X_{ji}) \in \{0, 1, 2, \dots\}^{J \times I}$ count mutations of type $i = 1, \dots, I$ in sample $j = 1, \dots, J$. The Poisson NMF model with $K$ latent processes is

$$X_{ji} \sim \mathrm{Poisson}\Big(\sum_{k=1}^K L_{jk} R_{ki}\Big) \quad\text{independently},$$

with nonnegative loadings $L \in \mathbb R_+^{J \times K}$ and signatures $R \in \mathbb R_+^{K \times I}$ whose rows sum to $1$ (each row $R_k$ is a probability vector over mutation types). Let $\theta$ collect all parameters, $\pi_0(\theta)$ be a prior density and $p(X \mid \theta)$ the Poisson likelihood.

**Definition.** For a power $\xi \in [0, 1]$, the **power posterior** is

$$\pi_\xi(\theta \mid X) = \frac{p(X \mid \theta)^{\xi}\, \pi_0(\theta)}{Z_\xi(X)}, \qquad Z_\xi(X) = \int p(X \mid \theta)^{\xi}\, \pi_0(\theta)\, d\theta,$$

whenever $0 < Z_\xi(X) < \infty$. It interpolates between the prior ($\xi = 0$) and the standard posterior ($\xi = 1$), and its log density is

$$\log \pi_\xi(\theta \mid X) = \text{const} + \log \pi_0(\theta) + \xi \sum_{j=1}^J \sum_{i=1}^I \log \mathrm{Poisson}\Big(X_{ji} \,\Big|\, \sum_k L_{jk} R_{ki}\Big),$$

so any sampler for the standard posterior targets $\pi_\xi$ after scaling the log-likelihood by $\xi$.

**Choosing the power.** $\xi$ is chosen by simulation: fit pilot signatures and loadings $(R^\star, L^\star)$ to the data, generate pilot data sets from perturbed data-generating processes anchored at them (well specified $X \sim \mathrm{Poisson}(L^\star R^\star)$; contaminated by a per-sample Dirichlet noise signature carrying a fraction $\alpha$ of each sample's total loading; per-sample Dirichlet perturbations of each signature at expected cosine error $\gamma$; negative binomial counts with variance $\kappa$ times the mean), and pick the $\xi$ that recovers the pilot signatures best across all of them.

## Depends on

- [Reconstruction matrix in nonnegative matrix factorization](recon.md)

## Remarks

Raising the likelihood to a power $\xi < 1$ is equivalent to treating the data as carrying only a fraction $\xi$ of their nominal information; for latent-variable models with unknown latent dimension this prevents the posterior from adding spurious components to absorb small systematic departures from the Poisson NMF model (over-dispersion, sample-specific perturbations of a signature, low-level noise). The power posterior of a misspecified model is closer in Kullback–Leibler divergence to the standard posterior of a more flexible well-specified model than the standard posterior of the misspecified model is. When the model is correct, $\xi = 1$ is ideal, and smaller $\xi$ reflects more severe misspecification.

## Sources

- C. Xue, J. W. Miller, S. L. Carter and J. H. Huggins, "Robust discovery of mutational signatures using power posteriors", PLoS Computational Biology 22 (2026), e1014372, Methods ("Model and sparsity-inducing prior", Eqs. (1)–(2); "The power posterior", Eqs. (6)–(8); "Choosing the power"; "Simulating data generating processes", Eq. (9)), <https://doi.org/10.1371/journal.pcbi.1014372>, PMCID PMC13274926.
