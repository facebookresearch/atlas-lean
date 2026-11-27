# Covariance-decay model of spatial allele frequencies and local-distance estimation of ancestry

**Model.** Genotypes $x_{i\ell}\in\{0,1,2\}$ are observed for $n$ individuals at $p$ SNPs; individual $i$ has an unknown ancestral location $\mathbf z_i\in\mathbb R^2$. For each SNP the allele-frequency surface $q_\ell(\mathbf z)$ is an independent sample path of a stationary random field with mean $\mu_\ell=\mathbb E\,q_\ell(\mathbf z)$ and a common, otherwise arbitrary, covariance decay function

$$\operatorname{cov}\big(q_\ell(\mathbf z),q_\ell(\mathbf z')\big)=\eta(\mathbf z-\mathbf z'),$$

and under Hardy–Weinberg equilibrium $x_{i\ell}\mid q_\ell(\mathbf z_i)\sim\mathrm{Binomial}(2,q_\ell(\mathbf z_i))$. This captures (possibly anisotropic) isolation by distance and contains earlier parametric spatial models (e.g. SCAT, SPA, SpaceMix) as special parametrizations of $\eta$.

**Estimators.** Define

$$\hat\mu_\ell=\frac1{2n}\sum_ix_{i\ell},\qquad \hat\eta_{ij}=\frac1p\sum_\ell\Big(\frac{x_{i\ell}}2-\hat\mu_\ell\Big)\Big(\frac{x_{j\ell}}2-\hat\mu_\ell\Big),\qquad \hat\eta_0=\frac1p\sum_\ell\Big(\frac1{2n}\sum_i\big(x_{i\ell}^2-x_{i\ell}\big)-\hat\mu_\ell^2\Big).$$

**Theorem (concentration).** Let $K_{ij}=\eta(\mathbf z_i-\mathbf z_j)$ and $\kappa=\mathbf 1^\top K\mathbf 1$ with $\mathbf 1=n^{-1/2}(1,\dots,1)^\top$. With probability at least $1-(n+1)^{-2}$, simultaneously for all $i\neq j$,

$$|\hat\eta_{ij}-\eta(\mathbf z_i-\mathbf z_j)|\le5\sqrt{\frac{2\log(n+1)}{p}}+16\sqrt{\frac\kappa n}+\frac8n,\qquad |\hat\eta_0-\eta(\mathbf 0)|\le5\sqrt{\frac{2\log(n+1)}{p}}+16\sqrt{\frac\kappa n}+\frac8n .$$

So with many SNPs and weak average relatedness ($\kappa/n\to0$), genotype covariances recover the covariance decay function at every pair of sampled locations.

**Local distances and embedding.** Because $\eta$ is maximal at $\mathbf 0$, $\nabla\eta(\mathbf 0)=\mathbf 0$ and $\nabla^2\eta(\mathbf 0)\preceq0$; with $J$ a square root of $-\frac12\nabla^2\eta(\mathbf 0)$,

$$\eta(\mathbf 0)-\eta(\mathbf z_i-\mathbf z_j)=\|J(\mathbf z_i-\mathbf z_j)\|^2+O(\|\mathbf z_i-\mathbf z_j\|^3),$$

so $\hat d_{ij}=(\hat\eta_0-\hat\eta_{ij})^{1/2}$ consistently estimates the $J$-transformed distance for nearby pairs. Keeping only pairs with $\hat d_{ij}\le\tau$ and embedding the resulting local distance graph (e.g. by ISOMAP shortest paths and multidimensional scaling), then fixing $J$ with a few anchor individuals of known location, reconstructs ancestry coordinates without assuming a parametric form for $\eta$. The estimated locations and spatially smoothed allele frequencies are then used as covariates to correct population stratification in association tests.

## Depends on

- [Offspring genotype law under random union of gametes](../../population-genetics/hardy-weinberg-law/offspring.md)

## Expansion

Conditional on the surfaces, $\mathbb E[(x_{i\ell}/2-\mu_\ell)(x_{j\ell}/2-\mu_\ell)]=\eta(\mathbf z_i-\mathbf z_j)$ for $i\ne j$, while for $i=j$ the binomial sampling adds a variance term that $x^2-x$ removes, which is why the diagonal uses $\hat\eta_0$. Independence across SNPs gives the $\sqrt{\log n/p}$ term by Hoeffding-type bounds and a union bound over pairs; replacing $\mu_\ell$ by $\hat\mu_\ell$ costs the $\sqrt{\kappa/n}$ and $1/n$ terms. PCA uses all pairwise covariances as if they were linear in distance, which distorts the map when $\eta$ decays nonlinearly; restricting to local pairs where the quadratic expansion is accurate avoids that bias.

## Sources

- Anand Bhaskar, Adel Javanmard, Thomas A. Courtade and David Tse, *Novel probabilistic models of spatial genetic ancestry with applications to stratification correction in genome-wide association studies*, Bioinformatics 33(6) (2017), 879–885. <https://doi.org/10.1093/bioinformatics/btw720> Section 3.1 (model), Supplementary Section 6.2 (algorithm, Theorem 1, local-distance step and ISOMAP embedding), Section 7 (association testing). Locators use the numbering of the preprint arXiv:1610.07306.
