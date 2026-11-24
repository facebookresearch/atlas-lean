# Oja's rule extracts the principal component

A linear neuron with weight vector $w$ responds to an input $x$ with $y = w^\top x$, and Oja's rule updates the weights by $w_{n+1} = w_n + \eta_n\, y_n (x_n - y_n w_n)$, a Hebbian step with multiplicative normalization. For inputs with correlation matrix $C$ whose largest eigenvalue $\lambda_1$ is simple, with unit eigenvector $q_1$, the weight vector of a single neuron trained by the rule converges to the first principal component $\pm q_1$, and the output variance $E[y_n^2]$ converges to $\lambda_1$, provided the learning rates satisfy $\sum_n \eta_n = \infty$ and $\sum_n \eta_n^p < \infty$ for some $p > 1$; the proofs use a Lyapunov-function analysis (Oja's rule, Wikipedia, section on stability and principal component analysis).

The averaged equation $\dot z = Cz - (z^\top C z)\, z$ shows the mechanism. Writing $z_j = z \cdot e_j$ in an orthonormal eigenbasis with $e_1 = q_1$ gives $\dot z_j = (\lambda_j - z^\top C z)\, z_j$, so $\frac{d}{dt} \ln |z_j / z_1| = \lambda_j - \lambda_1 < 0$ for $j \ne 1$ whenever $z_1(0) \ne 0$, and $\frac{d}{dt} |z|^2 = 2\, z^\top C z\, (1 - |z|^2)$. Hence, if $C$ is positive semidefinite with $\lambda_1 > 0$ and $z_1(0) \ne 0$, the direction of $z(t)$ tends to that of $\operatorname{sign}(z_1(0))\, q_1$, the quantity $z^\top C z$ is eventually bounded below by a positive constant, and $z(t) \to \operatorname{sign}(z_1(0))\, q_1$.


## Expansion

1. The model: the linear neuron, the input law with correlation matrix $C$, and the rule as a first-order expansion in $\eta$ of normalized Hebbian learning.
2. The averaged equation: the coordinate equations in the eigenbasis and the radial equation, and the convergence of the direction and of the norm to the leading eigenvector of $C$, the first loading vector of [principal component analysis](../../Probability/linear-models-multivariate/principal-component-analysis/README.md).
3. Linearization at $\pm q_1$, exponential stability, and instability of the other eigenvectors.
4. The stochastic rule and the ordinary differential equation method of stochastic approximation, with the boundedness conditions of Oja and Karhunen, giving almost sure convergence to $\pm q_1$.
5. Convergence of the output variance to $\lambda_1$.

## Sources

- Oja's rule, Wikipedia, sections on the formula and on stability and principal component analysis. <https://en.wikipedia.org/wiki/Oja%27s_rule>
- Original result: E. Oja, A simplified neuron model as a principal component analyzer, J. Math. Biol. 15 (1982), 267–273. <https://doi.org/10.1007/bf00275687> The rule and its convergence to the first principal component follow Oja's rule, Wikipedia.
- Original result: E. Oja and J. Karhunen, On stochastic approximation of the eigenvectors and eigenvalues of the expectation of a random matrix, J. Math. Anal. Appl. 106 (1985), 69–84. <https://doi.org/10.1016/0022-247x(85)90131-3> The stochastic-approximation convergence follows Oja's rule, Wikipedia.
