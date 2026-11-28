# Covariance shift (C-SHIFT) normalization of sample-bias in log gene expression

**Model.** Observed expression of gene $n$ in sample $i$ is distorted by a sample-wide multiplicative bias (e.g. variable RNA degradation): $\tilde X^{(i)}_n = W^{(i)}X^{(i)}_n$ with i.i.d. $W^{(i)} > 0$ independent of $X$. On the log scale $\tilde Y^{(i)}_n = Y^{(i)}_n + V^{(i)}$, $V = \log W$, and the empirical covariance matrices of the observed and true log-expressions of $M$ genes satisfy

$$C = \tilde C + \hat a\mathbf{1}^{\mathsf T} + \mathbf{1}\hat a^{\mathsf T} - \hat\omega\,\mathbf{1}\mathbf{1}^{\mathsf T}, \qquad \hat a_n = -\widehat{\mathrm{Cov}}(Y_n, V), \quad \hat\omega = \widehat{\mathrm{Var}}(V) > 0.$$

A large $\hat\omega$ shifts all covariances upwards and erases strong negative correlations; the aim is to recover $C$ from $\tilde C$.

**Proposition.** If $\mathcal{M}$ is symmetric positive definite, then

$$v^* := \max\{v : \mathcal{M} - v\,\mathbf{1}\mathbf{1}^{\mathsf T} \succeq 0\} = \frac{1}{\mathbf{1}^{\mathsf T}\mathcal{M}^{-1}\mathbf{1}},$$

and $\mathcal{M} - v^*\mathbf{1}\mathbf{1}^{\mathsf T}$ is singular.

**C-SHIFT estimator.** For $\alpha \in \mathbb{R}^M$ with $A_\alpha = \tilde C + \alpha\mathbf{1}^{\mathsf T} + \mathbf{1}\alpha^{\mathsf T} \succ 0$, set $v(\alpha) = 1/(\mathbf{1}^{\mathsf T}A_\alpha^{-1}\mathbf{1})$ and $C_\alpha = A_\alpha - v(\alpha)\mathbf{1}\mathbf{1}^{\mathsf T}$, the largest rank-one shift keeping the matrix positive semidefinite (so $\det C_\alpha = 0$). The normalised covariance is $C_{\alpha^*}$ with $\alpha^*$ minimising $\|C_\alpha\|_F^2$, motivated by the high-dimensional heuristic that the true covariance has the smallest Frobenius norm among admissible shifts (most gene pairs are nearly uncorrelated).

**Theorem.** If $\tilde C$ has full rank, $\alpha \mapsto \|C_\alpha\|_F^2$ is convex on its domain, with gradient

$$\tfrac14\nabla\|C_\alpha\|_F^2 = M\alpha + \tilde C\mathbf{1} + [a - Mv(\alpha)]\mathbf{1} + [M^2v(\alpha)^2 - c\,v(\alpha) - 2Ma\,v(\alpha)]A_\alpha^{-1}\mathbf{1},$$

where $a = \mathbf{1}^{\mathsf T}\alpha$ and $c = \mathbf{1}^{\mathsf T}\tilde C\mathbf{1}$; the minimiser can therefore be found by gradient descent. (If $\tilde C$ is singular, e.g. $N < M$, its diagonal is perturbed slightly first.)

## Proof sketch

For $\mathcal{M} \succ 0$, $\mathcal{M} - v\mathbf{1}\mathbf{1}^{\mathsf T} \succeq 0$ iff $x^{\mathsf T}\mathcal{M}x \ge v(\mathbf{1}^{\mathsf T}x)^2$ for all $x$, and by Cauchy–Schwarz in the $\mathcal{M}$-inner product $\min_{\mathbf{1}^{\mathsf T}x = 1}x^{\mathsf T}\mathcal{M}x = 1/(\mathbf{1}^{\mathsf T}\mathcal{M}^{-1}\mathbf{1})$, attained at $x \propto \mathcal{M}^{-1}\mathbf{1}$. Since the true $C$ is itself of the form $A_\alpha - \omega\mathbf{1}\mathbf{1}^{\mathsf T}$ with $\alpha = \hat a$, the family $\{C_\alpha\}$ contains matrices close to $C$, and convexity (shown via the Hessian) guarantees a unique basin. Simulations on random multiplicative gene cascades show recovery of strong negative correlations removed by the bias.

## Sources

- Evgenia Chunikhina, Paul Logan, Yevgeniy Kovchegov, Anatoly Yambartsev, Debashis Mondal and Andrey Morgun, "The C-SHIFT Algorithm for Normalizing Covariances", *IEEE/ACM Transactions on Computational Biology and Bioinformatics* 20 (2023), 720–730, <https://doi.org/10.1109/tcbb.2022.3151840>. Preprint version: arXiv:2003.12936 (2020), Section 1 (bias model, Proposition on the maximal rank-one shift, gradient and Hessian lemmas, convexity theorem), <https://doi.org/10.48550/arXiv.2003.12936>.
