# Node-age conditions for microergodicity of Ornstein–Uhlenbeck covariance parameters

Let $\mathbb{T}$ be an ultrametric phylogenetic tree with $n$ tips and $d_{ij}$ the path length between tips $i$ and $j$. In the Ornstein–Uhlenbeck (OU) tree model with stationary root, a trait evolves along the branches as an OU process $dY_t = -\alpha(Y_t - \mu)\,dt + \sigma\,dB_t$ with $\alpha > 0$, the root value is drawn from the stationary law $N(\mu,\gamma)$ with $\gamma = \sigma^2/(2\alpha)$, and the tip values are jointly Gaussian with mean $\mu$ and covariance

$$
\operatorname{cov}(Y_i, Y_j) = \gamma\, e^{-\alpha d_{ij}} .
$$

A function $f(\theta)$ of the parameter $\theta = (\mu,\alpha,\gamma)$ is **microergodic** for the law of the infinite tip sequence if $f(\theta_1) \neq f(\theta_2)$ implies that $P_{\theta_1}$ and $P_{\theta_2}$ are mutually singular; a parameter that is not microergodic cannot be estimated consistently. Asymptotics are taken along a nested sequence of trees $\mathbb{T}_1 \subset \mathbb{T}_2 \subset \cdots$, with $(T_i)_{i}$ the ages of all internal nodes (counted with multiplicity: a node with $d$ children counts $d-1$ times). Condition (C) says that the trees are nested and ultrametric and that the node ages are bounded.

For $t \ge 0$ define

$$
f_t(\gamma,\alpha) = \begin{cases} \gamma\left(1 - e^{-2\alpha t}\right), & t > 0, \\ \gamma\alpha = \sigma^2/2, & t = 0. \end{cases}
$$

Under condition (C) (Theorem 2.4):

1. If $t_0$ is a limit point of the node ages $(T_i)$, then $f_{t_0}(\gamma,\alpha)$ is microergodic. In particular, if node ages accumulate near the tips ($t_0 = 0$), the infinitesimal variance $\sigma^2$ is microergodic.
2. If $\sum_i (T_i - t)^2 = \infty$ for every $t \ge 0$, then $(\gamma,\alpha)$ is microergodic; this holds whenever $(T_i)$ has at least two limit points.

On symmetric trees with $m$ levels, internal nodes at level $i$ having $d_i$ children along branches of length $t_i$ (Theorem 2.7):

- (Increasing node degrees.) If $m$ and $t_1,\dots,t_m$ are fixed, $d_1,\dots,d_{m-1}$ are fixed and $d_m \to \infty$, so that $t_m > 0$ is the only limit point of the node ages, then $(\gamma,\alpha)$ is not microergodic.
- (Dense sampling.) If the number of levels grows, every node has $d$ children, nodes at level $k$ have age $u_k = q^k + t_0$ with $0 < q < 1$, and $dq^2 < 1$ (so the divergence condition in item 2 fails), then $(\gamma,\alpha)$ is not microergodic when $t_0 = 0$ but is microergodic when $t_0 > 0$.

## Depends on

- [Inconsistency of the Ornstein–Uhlenbeck mean on bounded trees](inconsistency-of-the-ornstein-uhlenbeck-mean-on-bounded-trees.md)

## Expansion

The proofs compare Gaussian measures through their entropy distance using independent contrasts: the contrast between two subtrees below an internal node of age $T_i$ is distributed as $N(0, 2\gamma(1 - e^{-2\alpha T_i}))$, and contrasts on disjoint paths are independent (Lemma 2.5). Infinitely many contrasts at ages accumulating at $t_0$ therefore identify $f_{t_0}(\gamma,\alpha)$, and two different limit points identify $(\gamma,\alpha)$ because $f_{t_1}$ and $f_{t_2}$ together determine both parameters (Lemma 2.6). On symmetric trees the covariance matrix has explicit eigenvalues with multiplicities governed by the $d_i$, which settles the boundary cases. The dense-sampling example shows that node ages accumulating only at the tips, as in densely sampled recent radiations, need not make $\alpha$ and $\gamma$ separately estimable.

## Sources

- Lam Si Tung Ho, Cécile Ané, Asymptotic theory with hierarchical autocorrelation: Ornstein-Uhlenbeck tree models, arXiv:1306.1322 (2013). <https://doi.org/10.48550/arXiv.1306.1322>. Published version: The Annals of Statistics 41(2) (2013), 957–981, <https://doi.org/10.1214/13-aos1105>; locators above refer to the arXiv version.
