# Unequal REML convergence rates of Ornstein–Uhlenbeck tree parameters

Let $\mathbb{T}$ be an ultrametric phylogenetic tree with $n$ tips and $d_{ij}$ the path length between tips $i$ and $j$. In the Ornstein–Uhlenbeck (OU) tree model with stationary root, a trait evolves along the branches as an OU process $dY_t = -\alpha(Y_t - \mu)\,dt + \sigma\,dB_t$ with $\alpha > 0$, the root value is drawn from the stationary law $N(\mu,\gamma)$ with $\gamma = \sigma^2/(2\alpha)$, and the tip values are jointly Gaussian with mean $\mu$ and covariance

$$
\operatorname{cov}(Y_i, Y_j) = \gamma\, e^{-\alpha d_{ij}} .
$$

A function $f(\theta)$ of the parameter $\theta = (\mu,\alpha,\gamma)$ is **microergodic** for the law of the infinite tip sequence if $f(\theta_1) \neq f(\theta_2)$ implies that $P_{\theta_1}$ and $P_{\theta_2}$ are mutually singular; a parameter that is not microergodic cannot be estimated consistently. Asymptotics are taken along a nested sequence of trees $\mathbb{T}_1 \subset \mathbb{T}_2 \subset \cdots$, with $(T_i)_{i}$ the ages of all internal nodes (counted with multiplicity: a node with $d$ children counts $d-1$ times). Condition (C) says that the trees are nested and ultrametric and that the node ages are bounded.

Consider symmetric trees with a fixed number $m$ of levels and fixed branch lengths $t_1,\dots,t_m$, internal nodes at level $i$ having $d_i$ children, $n = d_1 \cdots d_m$ tips, and $\tilde n = n/d_m = d_1\cdots d_{m-1} \to \infty$ (which makes $\gamma$ and $\alpha$ microergodic). Let $\nu = \gamma(1 - e^{-2\alpha t_m})$. Then the restricted maximum likelihood (REML) estimator $(\hat\nu,\hat\alpha)$ is consistent and (Theorem 3.1)

$$
\begin{pmatrix} \sqrt{n}\,(\hat\nu - \nu) \\ \sqrt{\tilde n}\,(\hat\alpha - \alpha) \end{pmatrix} \xrightarrow{d} N\!\left(\mathbf{0}, \begin{pmatrix} 8\nu^2 & 0 \\ 0 & v_\alpha \end{pmatrix}\right)
$$

for an explicit $v_\alpha > 0$. Moreover, if $n/\tilde n = d_m \to \infty$, then $\sqrt{\tilde n}\,(\hat\gamma - \gamma, \hat\alpha - \alpha)$ converges to a centered normal law, and the asymptotic correlation between $\log\hat\gamma$ and $\log(1 - e^{-2\hat\alpha t_m})$ is $-1$.

## Depends on

- [Node-age conditions for microergodicity of Ornstein–Uhlenbeck covariance parameters](node-age-conditions-for-microergodicity-of-ornstein-uhlenbeck-covariance-parameters.md)

## Expansion

$\nu = f_{t_m}(\gamma,\alpha)$ is microergodic using only the single limit point $t_m$, so it is learned from all $n$ tips at the usual rate $n^{-1/2}$; separating $\gamma$ from $\alpha$ needs contrasts at other ages, of which there are only of order $\tilde n$, so $\hat\alpha$ and $\hat\gamma$ converge at the slower rate $\tilde n^{-1/2}$, and their errors are almost perfectly confounded along the curve of constant $\nu$. Simulations on a 4507-species mammal tree in the paper show the same pattern for maximum likelihood: the selection strength is estimated far less precisely than the stationary variance combination.

## Sources

- Lam Si Tung Ho, Cécile Ané, Asymptotic theory with hierarchical autocorrelation: Ornstein-Uhlenbeck tree models, arXiv:1306.1322 (2013). <https://doi.org/10.48550/arXiv.1306.1322>. Published version: The Annals of Statistics 41(2) (2013), 957–981, <https://doi.org/10.1214/13-aos1105>; locators above refer to the arXiv version.
