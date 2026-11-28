# Entry point of the Laplacian-net logistic regularization path

**Setting.** Let $y \in \{0,1\}^n$ be a binary clinical response and $X \in \mathbb R^{n \times p}$ standardized expression values of $p$ genes, with rows $X_i$. Let $G = (V, E)$ be a gene network on the $p$ genes with adjacency $e_{uv} \in \{0,1\}$, degrees $d_u = \sum_v e_{uv} \ge 1$, $D = \mathrm{diag}(d_u)$, and normalized Laplacian

$$\mathcal L = I - D^{-1/2} E D^{-1/2}, \qquad \beta^{\top}\mathcal L\beta = \sum_{\{u,v\} : e_{uv} = 1}\Big(\frac{\beta_u}{\sqrt{d_u}} - \frac{\beta_v}{\sqrt{d_v}}\Big)^2 .$$

For $\lambda \ge 0$ and $\alpha \in [0,1]$ the **Laplacian-net logistic** (Logit-Lapnet) estimator minimizes the convex criterion

$$\mathcal J(\beta) = \sum_{i=1}^{n}\Big[-y_iX_i\beta + \ln\big(1 + e^{X_i\beta}\big)\Big] + \lambda\alpha\|\beta\|_1 + \lambda(1-\alpha)\,\beta^{\top}\mathcal L\beta .$$

It reduces to lasso logistic regression at $\alpha = 1$ and to the elastic net when $\mathcal L$ is replaced by $I$.

**Proposition.** For $\alpha \in (0, 1]$, $\beta = 0$ minimizes $\mathcal J$ if and only if

$$\lambda \ \ge\ \lambda_0 := \frac{\|X^{\top}(y - \tfrac12\mathbf 1)\|_\infty}{\alpha}.$$

In particular $\lambda_0$ is the entry point of the path: $\hat\beta = 0$ for $\lambda \ge \lambda_0$ and $\hat\beta \ne 0$ for $0 < \lambda < \lambda_0$, and

$$\lambda_0 \ \le\ \frac{1}{2\alpha}\Big(2\|X^{\top}y\|_\infty + \Big\|\sum_{i=1}^{n}X_i^{\top}\Big\|_\infty\Big),$$

so the path must start at larger penalties as $\alpha$ decreases toward the pure Laplacian penalty.

## Expansion

The criterion is convex because the logistic loss is convex, $\|\cdot\|_1$ is convex and $\mathcal L$ is positive semidefinite. At $\beta = 0$ the gradient of the loss is $X^{\top}(\sigma(0)\mathbf 1 - y) = X^{\top}(\tfrac12\mathbf 1 - y)$ and the gradient of the quadratic penalty is $0$, so the subgradient optimality condition $0 \in X^{\top}(\tfrac12\mathbf 1 - y) + \lambda\alpha\,\partial\|\cdot\|_1(0)$, with $\partial\|\cdot\|_1(0) = [-1,1]^p$, holds exactly when $\|X^{\top}(y - \tfrac12\mathbf 1)\|_\infty \le \lambda\alpha$. The displayed upper bound follows from the triangle inequality $\|X^{\top}y - \tfrac12X^{\top}\mathbf 1\|_\infty \le \|X^{\top}y\|_\infty + \tfrac12\|X^{\top}\mathbf 1\|_\infty$.

## Sources

- W. Zhang, Y.-W. Wan, G. I. Allen, K. Pang, M. L. Anderson, Z. Liu, "Molecular pathway identification using biological network-regularized logistic models", BMC Genomics (2013), Methods: Eqs. (1)–(4) (Logit-Lapnet criterion), and Lemma 2 (bound on the maximal penalty), <https://doi.org/10.1186/1471-2164-14-S8-S7>, PMCID PMC4046566.
