# Oja's rule extracts the principal component

A linear neuron with weight vector $w$ responds to an input $x$ with $y = w^\top x$, and Oja's rule updates the weights by $w_{n+1} = w_n + \eta_n\, y_n (x_n - y_n w_n)$, a Hebbian step with multiplicative normalization. For inputs with correlation matrix $C = E[x x^\top]$, the rule averaged over the input law is the ordinary differential equation

$$\dot z = Cz - (z^\top C z)\, z,$$

and this page states its convergence. Let $C$ be symmetric positive semidefinite with simple largest eigenvalue $\lambda_1 > 0$ and unit eigenvector $q_1$, and let $z(0) \in \mathbb R^d$ satisfy $q_1^\top z(0) \ne 0$. Then the solution exists for all $t \ge 0$ and $z(t) \to \operatorname{sign}(q_1^\top z(0))\, q_1$ as $t \to \infty$; in particular $z(t)^\top C z(t) \to \lambda_1$, the variance of the output along the limit direction.

The mechanism: writing $z_j = z \cdot e_j$ in an orthonormal eigenbasis with $e_1 = q_1$ gives $\dot z_j = (\lambda_j - z^\top C z)\, z_j$, so $z_1(t)$ keeps the sign of $z_1(0)$, $\frac{d}{dt} \ln |z_j / z_1| = \lambda_j - \lambda_1 < 0$ for $j \ne 1$, and $\frac{d}{dt} |z|^2 = 2\, z^\top C z\, (1 - |z|^2)$. Hence the direction of $z(t)$ tends to that of $\operatorname{sign}(z_1(0))\, q_1$, the quantity $z^\top C z$ is eventually bounded below by a positive constant, and $|z(t)| \to 1$.

The stochastic rule itself is not covered by this statement: with i.i.d. inputs, step sizes $\sum_n \eta_n = \infty$, $\sum_n \eta_n^2 < \infty$ and $w_0 \ne 0$, a finite step can still land on an invariant state orthogonal to $q_1$ (for inputs $e_1$ with probability $3/4$ and $e_2$ with probability $1/4$, $w_0 = (1, 1)$ and $\eta_0 = 1$, the first step gives $w_1 = e_2$ with probability $1/4$, after which $w_n = e_2$ for all $n$). Its almost-sure convergence under the hypotheses of Oja and Karhunen is a separate target in the Expansion.

## Expansion

1. The model: the linear neuron, the input law with correlation matrix $C$, and the rule as a first-order expansion in $\eta$ of normalized Hebbian learning.
2. The averaged equation: the coordinate equations in the eigenbasis and the radial equation, and the convergence of the direction and of the norm to the leading eigenvector of $C$, the first loading vector of [principal component analysis](../../Probability/linear-models-multivariate/principal-component-analysis/README.md).
3. Linearization at $\pm q_1$, exponential stability, and instability of the other eigenvectors.
4. Separate target: the stochastic rule. State the exact hypotheses of Oja and Karhunen (1985) on the inputs, the step sizes and the boundedness of the iterates, including a condition that keeps the iterates off the invariant subspace orthogonal to $q_1$, and prove almost-sure convergence to $\pm q_1$ by the ordinary differential equation method of stochastic approximation.
5. Convergence of the output variance to $\lambda_1$, for the averaged equation and, under the hypotheses of item 4, for the stochastic rule.

## Sources

- Oja's rule, Wikipedia, sections on the formula and on stability and principal component analysis. <https://en.wikipedia.org/wiki/Oja%27s_rule>
- Original result: E. Oja, A simplified neuron model as a principal component analyzer, J. Math. Biol. 15 (1982), 267–273. <https://doi.org/10.1007/bf00275687> The rule and its convergence to the first principal component follow Oja's rule, Wikipedia.
- Original result: E. Oja and J. Karhunen, On stochastic approximation of the eigenvectors and eigenvalues of the expectation of a random matrix, J. Math. Anal. Appl. 106 (1985), 69–84. <https://doi.org/10.1016/0022-247x(85)90131-3> The stochastic-approximation convergence follows Oja's rule, Wikipedia.
