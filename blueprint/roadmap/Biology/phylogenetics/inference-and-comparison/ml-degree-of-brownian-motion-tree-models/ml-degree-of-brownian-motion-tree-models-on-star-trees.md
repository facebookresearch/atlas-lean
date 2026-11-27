# Maximum-likelihood degree of Brownian motion tree models on star trees and root invariance

**Model.** Let $\mathcal{T}$ be a rooted phylogenetic tree with leaves $1,\ldots,n$ and nonnegative edge lengths $t_e$. The *Brownian motion tree (BMT) model* is the Gaussian model of trait values at the leaves under Brownian motion along $\mathcal{T}$: the covariance matrix $\Sigma$ has

$$\Sigma_{ij} = \sum_{e \in \mathrm{path}(\rho,\ \mathrm{mrca}(i,j))} t_e ,$$

the length shared by the root-to-leaf paths of $i$ and $j$. Equivalently one adds the root as an extra leaf $0$ and parametrizes the concentration matrix $K = \Sigma^{-1}$ by edge parameters $\theta_e$. The *ML degree* is the number of complex critical points of the log-likelihood $\ell(K\mid S) = \log\det K - \operatorname{tr}(SK)$ on the model for a generic sample covariance $S$.

**Theorem (star trees).** The ML degree of the BMT model on the star tree with $n+1$ leaves (root included as leaf $0$) is

$$2^{n+1} - 2(n+1) - 1 .$$

**Theorem (root invariance).** BMT models on phylogenetic trees with the same unlabeled, unrooted topology have the same ML degree; in particular the ML degree does not depend on which leaf is the root.

**Determinant formula.** For any phylogenetic tree,

$$\det K_{\mathcal{T}}(\theta) = \Big(\prod_{e} \theta_e\Big)\prod_{v\ \mathrm{internal}}\Big(\sum_{\ell\ \mathrm{leaf}}\ \prod_{e \in v \leadsto \ell}\theta_e\Big)^{\deg(v)-2};$$

for the star tree this is $\prod_{i=0}^n\theta_i\,\big(\sum_{i=0}^n\theta_i\big)^{n-1}$, and the score equations read

$$\frac{1}{\theta_i} + \frac{n-1}{\theta_0+\cdots+\theta_n} - \sum_{j\ne i} c_{ij}\theta_j = 0,\qquad i = 0,\ldots,n,$$

with $c_{0j} = s_{jj}$ and $c_{ij} = s_{ii}+s_{jj}-2s_{ij}$ for $i > 0$.

## Expansion

In the coordinates $p_{ij} = -k_{ij}$ ($i,j>0$) and $p_{0i} = \sum_j k_{ij}$, the model is toric: $p_{ij}$ is the product of edge parameters along the path from $i$ to $j$, symmetric in all $n+1$ leaves including the root, which is why the ML degree depends only on the unrooted topology. The path map is $2^{\#\mathrm{internal}}$-to-one, so critical points can be counted in $\theta$ coordinates and divided by that factor. For the star tree the score equations are counted by a Bézout bound minus the solutions at infinity and on coordinate hyperplanes, whose multiplicities are computed by standard monomials in local rings, leaving $2^{n+1}-2(n+1)-1$.

## Sources

- Jane Ivy Coons, Shelby Cox, Aida Maraj and Ikenna Nometa, "ML degrees of Brownian motion tree models: Star trees and root invariance", Journal of Symbolic Computation 132 (2026), 102482, <https://doi.org/10.1016/j.jsc.2025.102482>; numbering as in arXiv:2402.10322: main theorems stated in Section 1 (star-tree ML degree; root invariance), determinant formula and score equations (Section "Score Equations").
