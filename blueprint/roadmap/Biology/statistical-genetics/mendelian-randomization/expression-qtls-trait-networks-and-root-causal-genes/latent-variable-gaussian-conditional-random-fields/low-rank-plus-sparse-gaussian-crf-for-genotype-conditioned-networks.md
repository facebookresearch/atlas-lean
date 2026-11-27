# Low-rank plus sparse Gaussian conditional random field for genotype-conditioned networks

**Model.** Let $Y \in \mathbb R^{m+p+h}$ be zero-mean with blocks $Y_Z$ (inputs conditioned on, e.g. $m$ genotypes), $Y_X$ ($p$ observed traits, e.g. metabolite levels) and $Y_H$ ($h$ hidden variables). Assume a Gaussian conditional random field

$$\begin{pmatrix} Y_X \\ Y_H \end{pmatrix} \Big|\, Y_Z \sim \mathcal N\!\left(-M^{-1}\begin{pmatrix} M_{ZX}^{\mathsf T} \\ M_{ZH}^{\mathsf T}\end{pmatrix} Y_Z,\; M^{-1}\right), \qquad M = \begin{pmatrix} M_X & M_{XH} \\ M_{XH}^{\mathsf T} & M_H \end{pmatrix} \succ 0,$$

with no distributional assumption on $Y_Z$. Zeros of $M_X$ encode conditional independences among traits given everything else, and zeros of $M_{ZX}$ encode absent direct input effects. Marginalizing the hidden block gives

$$Y_X \mid Y_Z \sim \mathcal N\big(-(S_X - L_X)^{-1}(S_{ZX} - L_{ZX})^{\mathsf T} Y_Z,\ (S_X - L_X)^{-1}\big),$$

where $S_X = M_X$, $S_{ZX} = M_{ZX}$, $L_X = M_{XH} M_H^{-1} M_{XH}^{\mathsf T}$ and $L_{ZX} = M_{ZH} M_H^{-1} M_{XH}^{\mathsf T}$. Thus $L_X \succeq 0$ and the stacked matrix $L = \begin{pmatrix} L_X \\ L_{ZX}\end{pmatrix}$ has rank at most $h$, while $S = \begin{pmatrix} S_X \\ S_{ZX}\end{pmatrix}$ is sparse when the networks are sparse; only the differences $S_X - L_X$ and $S_{ZX} - L_{ZX}$ are identified from data.

**Log-likelihood.** With sample covariances $\Sigma^n_Z$, $\Sigma^n_X$, $\Sigma^n_{ZX}$,

$$\ell = \log\det(S_X - L_X) - \operatorname{tr}\big(\Sigma^n_X (S_X - L_X)\big) - 2\operatorname{tr}\big(\Sigma^n_{ZX}(S_{ZX} - L_{ZX})^{\mathsf T}\big) - \operatorname{tr}\big((S_X - L_X)^{-1}(S_{ZX}-L_{ZX})^{\mathsf T}\Sigma^n_Z (S_{ZX}-L_{ZX})\big).$$

**Estimator.** Solve

$$\min_{S, L}\ -\ell(S_X, L_X, S_{ZX}, L_{ZX}) + \lambda_n\big(\gamma \|S\|_1 + \|L\|_*\big) \quad \text{s.t. } S_X - L_X \succ 0,\ L_X \succeq 0,$$

with $\|\cdot\|_1$ the entrywise $\ell_1$ norm and $\|\cdot\|_*$ the nuclear norm. The objective is jointly convex over a convex constraint set. Under rank-sparsity incoherence conditions on $(S^*, L^*)$ with $\gamma$ in a prescribed range and irrepresentability-type conditions on the Fisher information, with $\lambda_n$ of the prescribed order, the estimator recovers $(S^*, L^*)$ with high probability, and in the scaling regime where $S^*$ has degree of order $\log(p+m)^b$ and the number of latent factors is of order $p/\log(p+m)^{2b}$, roughly $n \gtrsim p \log(p+m)^{4b}$ samples suffice for $\max(\|\hat S - S^*\|_\infty/\gamma,\ \|\hat L - L^*\|_2) = o_P(1)$.

## Depends on

- [Gaussian conditioning (Schur complement)](../../../../../Probability/distributions/continuous/gaussian-conditioning/cond-distrib-multivariate-gaussian.md)

## Expansion

The marginal law follows from Gaussian marginalization in information form: integrating out $Y_H$ replaces the precision $M$ by its Schur complement $M_X - M_{XH}M_H^{-1}M_{XH}^{\mathsf T}$ and the linear coefficient $M_{ZX}^{\mathsf T}$ by $M_{ZX}^{\mathsf T} - M_{XH}M_H^{-1}M_{ZH}^{\mathsf T}$. Hidden factors therefore add a low-rank correction to both the trait network and the input-to-trait map. The estimator combines a sparse Gaussian conditional random field (which conditions on inputs but ignores latent confounding) with the low-rank plus sparse graphical lasso (which models latent factors but treats inputs as jointly Gaussian). Conditioning on genotypes uses them as anchors for edges between metabolites, while the nuclear-norm term absorbs confounders such as unmeasured environment. The consistency proof follows the low-rank plus sparse latent-variable graphical model analysis, adapted to the non-square input block and the conditional likelihood.

## Sources

- B. Frot, L. Jostins, G. McVean, "Graphical model selection for Gaussian conditional random fields in the presence of latent variables", Journal of the American Statistical Association 114(526):723-734 (2019), Equations 2.1, 2.2 and 2.4 and Theorem 1 (Section 3), <https://doi.org/10.1080/01621459.2018.1434531>, PMCID PMC6636895.
