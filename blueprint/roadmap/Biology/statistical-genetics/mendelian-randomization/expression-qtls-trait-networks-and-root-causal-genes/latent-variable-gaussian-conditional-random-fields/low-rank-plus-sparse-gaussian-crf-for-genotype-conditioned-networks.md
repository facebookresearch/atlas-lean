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

with $\|\cdot\|_1$ the entrywise $\ell_1$ norm and $\|\cdot\|_*$ the nuclear norm. The objective is jointly convex over a convex constraint set. **Recovery (Theorem 1 of the source).** Write $\|\cdot\|_2$ for the largest singular value, $\psi_Z = \|\Sigma^n_Z\|_2$, $\psi^*_X = \|(S^*_X - L^*_X)^{-1}\|_2$, $\xi(T(L^*))$ and $\mu(\Omega(S^*))$ for the incoherence measures of the low-rank and sparse parts, and

$$M = \max\Big(1,\ \frac{\psi_Z}{4\psi^*_X}\Big(1 + \sqrt{m/p}\Big)^2\Big), \qquad \lambda_n = \frac{Q_3}{\xi(T(L^*))}\sqrt{\frac{256\,(\psi^*_X)^2\,pM}{n}}.$$

Assume rank-sparsity incoherence of $(S^*, L^*)$ with $\gamma$ in the prescribed range (Assumption 1) and irrepresentability-type conditions on the Fisher information (Assumption 2), and that

- (a) the sample size satisfies $n \ge \frac{pM}{\xi(T(L^*))^4}\max\big(2,\ 256(\psi^*_X)^2/W^2\big)$, where $W>0$ is an explicit quantity depending on $\psi^*_X$, $\psi_Z$ and $\|S^*_{ZX} - L^*_{ZX}\|_2$;
- (b) the minimum nonzero singular value $\sigma$ of $L^*$ and the minimum magnitude $\theta$ of a nonzero entry of $S^*$ satisfy $\sigma \ge Q_4\lambda_n/\xi(T(L^*))^2$ and $\theta \ge Q_5\lambda_n/\mu(\Omega(S^*))$.

Here $Q_1,\dots,Q_6$ are constants defined in the source. Then, with probability at least $1 - \max\big(2e^{-pM},\ e^{-cpM}\big)$ for a constant $c>0$ depending on $\psi^*_X$ and $\psi_Z$ (explicit in the source), the estimator has $\operatorname{sign}(\hat S) = \operatorname{sign}(S^*)$, $\operatorname{rank}(\hat L) = \operatorname{rank}(L^*)$ and $\hat L_X \succeq 0$, and

$$\max\Big(\tfrac1\gamma\|\hat S - S^*\|_\infty,\ \|\hat L - L^*\|_2\Big) \le \frac{Q_6\,\psi^*_X}{\xi(T(L^*))}\sqrt{\frac{pM}{n}}.$$

In the scaling regime where $S^*$ has degree of order $\log(p+m)^b$ and the number of latent factors is of order $p/\log(p+m)^{2b}$, condition (a) amounts to $n \gtrsim p\,\log(p+m)^{4b}\,M$, which also gives $\max(\|\hat S - S^*\|_\infty/\gamma,\ \|\hat L - L^*\|_2) = o_P(1)$.

## Depends on

- [Gaussian conditioning (Schur complement)](../../../../../Probability/distributions/continuous/gaussian-conditioning/cond-distrib-multivariate-gaussian.md)

## Expansion

The marginal law follows from Gaussian marginalization in information form: integrating out $Y_H$ replaces the precision $M$ by its Schur complement $M_X - M_{XH}M_H^{-1}M_{XH}^{\mathsf T}$ and the linear coefficient $M_{ZX}^{\mathsf T}$ by $M_{ZX}^{\mathsf T} - M_{XH}M_H^{-1}M_{ZH}^{\mathsf T}$. Hidden factors therefore add a low-rank correction to both the trait network and the input-to-trait map. The estimator combines a sparse Gaussian conditional random field (which conditions on inputs but ignores latent confounding) with the low-rank plus sparse graphical lasso (which models latent factors but treats inputs as jointly Gaussian). Conditioning on genotypes uses them as anchors for edges between metabolites, while the nuclear-norm term absorbs confounders such as unmeasured environment. The consistency proof follows the low-rank plus sparse latent-variable graphical model analysis, adapted to the non-square input block and the conditional likelihood.

## Sources

- B. Frot, L. Jostins, G. McVean, "Graphical model selection for Gaussian conditional random fields in the presence of latent variables", Journal of the American Statistical Association 114(526):723-734 (2019), Equations 2.1, 2.2 and 2.4 and Theorem 1 (Section 3), <https://doi.org/10.1080/01621459.2018.1434531>, PMCID PMC6636895.
