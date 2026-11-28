# Progression-dependent quadratic gene-regulation model and its Bayesian lasso fit

**Model.** Along a latent progression score $s$ (for example from [Temporal progression distance from accumulated random walks](temporal-progression-distance-from-accumulated-random-walks.md)), the expression levels $X_1(s), \dots, X_n(s)$ of $n$ genes in a tumor cohort follow mass-action dynamics

$$\frac{dX_i}{ds} = \sum_{j \ne i} a_{ij}\, X_i(s)\, X_j(s) - d_i\, X_i(s), \qquad i = 1, \dots, n,$$

where $a_{ij}$ is the regulatory coefficient of gene $j$ on gene $i$ (positive: activation, negative: repression) and $d_i > 0$ is the self-degradation rate.

**Discretization and regression.** Take $m+1$ points $s_k = s(r_k)$, $r_k = k/m$, on the smoothed trajectory and set $Y_{ik} = \big(X_i(s_{k+1}) - X_i(s_k)\big)/(s_{k+1} - s_k)$. With $A_i = (a_{i1}, \dots, a_{in}, -d_i)$ and the $(n+1) \times (m+1)$ design matrix $X^{(i)}$ whose column $k$ is $\big(X_1(s_k)X_i(s_k), \dots, X_n(s_k)X_i(s_k), X_i(s_k)\big)^{\mathsf T}$, the model becomes the linear regression

$$Y_i = A_i X^{(i)} + \varepsilon_i, \qquad \varepsilon_{ik} \overset{\text{iid}}{\sim} \mathcal N(0, \sigma_i^2).$$

**Bayesian lasso.** With prior $A_i \mid \sigma_i^2, \lambda_i \sim \mathrm{Laplace}(0, \sigma_i/\lambda_i)$ (fixed shrinkage $\lambda_i$), an inverse-gamma prior on $\sigma_i^2$, and Gaussian likelihood $\prod_k \phi(Y_{ik}; A_i X^{(i)}_k, \sigma_i^2)$, the posterior

$$\pi(A_i, \sigma_i^2 \mid Y_i, X^{(i)}) \propto \pi(A_i \mid \sigma_i^2, \lambda_i)\, \pi(\sigma_i^2)\, \prod_{k=0}^m \phi\big(Y_{ik}; A_i X^{(i)}_k, \sigma_i^2\big)$$

is sampled by Gibbs MCMC, and an edge $j \to i$ is declared present when the 95% credible interval of $a_{ij}$ excludes $0$.

**Stability statement.** If two progression trajectories $s(r)$ and $\tilde s(r)$, $r \in [0, 1]$, share the same root and the coefficients $(a_{ij}, d_i)$ and $(\tilde a_{ij}, \tilde d_i)$ make the model hold along each, and if for every $i$ the functions $X_i X_j$ ($j \ne i$) and $X_i$ are linearly independent along the trajectory $s$ (so the coefficients are identifiable), then $\sum_{i,j} |\tilde a_{ij} - a_{ij}|^2 \to 0$ as $\|\tilde s - s\|_{L^2[0,1]} \to 0$: small perturbations of the inferred ordering perturb the inferred network only slightly.

## Depends on

- [Temporal progression distance from accumulated random walks](temporal-progression-distance-from-accumulated-random-walks.md)

## Expansion

The right-hand side is linear in the unknowns $(a_{i1}, \dots, a_{in}, d_i)$ for each $i$ separately, so a forward-difference approximation of $dX_i/ds$ on a fine grid of the reconstructed trajectory turns network inference into $n$ independent linear regressions with products $X_iX_j$ as features. The Laplace prior is the Bayesian counterpart of the $\ell_1$ penalty, favoring sparse networks, and its scale-mixture-of-normals representation gives conjugate full conditionals for Gibbs sampling. The stability statement follows because the coefficients are recovered from the trajectory by a continuous map (least-squares on a nondegenerate design), so they depend continuously on $s$.

## Sources

- X. Sun, J. Zhang, Q. Nie, "Inferring latent temporal progression and regulatory networks from cross-sectional transcriptomic data of cancer samples", *PLoS Computational Biology* 17(3) (2021) e1008379. Methods, "Dynamical systems modeling" (Eq. (10)), "Parameter estimation using Bayesian Lasso method" (Eqs. (11)–(19)) and "Mathematical analysis" (Theorem 1; proof in S2 Text). <https://doi.org/10.1371/journal.pcbi.1008379>. PMCID: PMC7968745.
