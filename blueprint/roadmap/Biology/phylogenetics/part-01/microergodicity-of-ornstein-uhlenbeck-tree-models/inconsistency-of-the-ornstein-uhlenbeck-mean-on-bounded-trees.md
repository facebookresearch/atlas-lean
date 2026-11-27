# Inconsistency of the Ornstein–Uhlenbeck mean on bounded trees

Let $\mathbb{T}$ be an ultrametric phylogenetic tree with $n$ tips and $d_{ij}$ the path length between tips $i$ and $j$. In the Ornstein–Uhlenbeck (OU) tree model with stationary root, a trait evolves along the branches as an OU process $dY_t = -\alpha(Y_t - \mu)\,dt + \sigma\,dB_t$ with $\alpha > 0$, the root value is drawn from the stationary law $N(\mu,\gamma)$ with $\gamma = \sigma^2/(2\alpha)$, and the tip values are jointly Gaussian with mean $\mu$ and covariance

$$
\operatorname{cov}(Y_i, Y_j) = \gamma\, e^{-\alpha d_{ij}} .
$$

A function $f(\theta)$ of the parameter $\theta = (\mu,\alpha,\gamma)$ is **microergodic** for the law of the infinite tip sequence if $f(\theta_1) \neq f(\theta_2)$ implies that $P_{\theta_1}$ and $P_{\theta_2}$ are mutually singular; a parameter that is not microergodic cannot be estimated consistently. Asymptotics are taken along a nested sequence of trees $\mathbb{T}_1 \subset \mathbb{T}_2 \subset \cdots$, with $(T_i)_{i}$ the ages of all internal nodes (counted with multiplicity: a node with $d$ children counts $d-1$ times). Condition (C) says that the trees are nested and ultrametric and that the node ages are bounded.

1. Under condition (C), the optimum $\mu$ is not microergodic, so no estimator of $\mu$ is consistent (Theorem 2.1).
2. On a single ultrametric tree of height $T$ whose root has $k$ children, the shortest of the root's branches having length $t$, let $\hat\mu$ be the maximum likelihood estimator of $\mu$ computed with a possibly wrong value $\alpha_*$ of $\alpha$. Then (Theorem 2.2)

$$
\operatorname{var}(\hat\mu) \;\ge\; \frac{\sigma^2}{2\alpha}\, e^{-2\alpha T}\left(1 + \frac{e^{2\alpha t} - 1}{k}\right),
$$

with equality if and only if $\alpha_* = \alpha$ and the tree is a star whose only internal node is the root (then $k = n$ and $t = T$). Consequently, if $T$ stays bounded as $n$ grows and $\alpha > 0$, then $\hat\mu$ is not consistent.

## Expansion

The bound follows from $(\mathbf{1}^{\top} V_\alpha^{-1} \mathbf{1})^{-1} \ge e^{-2\alpha T} + k^{-1}(e^{-2\alpha(T-t)} - e^{-2\alpha T})$ for $V_\alpha = (e^{-\alpha d_{ij}})$ (Lemma 2.3): however many tips are added, all of them share the information carried by the root value, whose correlation with every tip is at least $e^{-\alpha T}$. The best possible design, a star tree, still leaves variance $\gamma e^{-2\alpha T}(1 + (e^{2\alpha T}-1)/n) \to \gamma e^{-2\alpha T} > 0$. This mirrors the inconsistency of the mean under infill asymptotics for spatial OU fields.

## Sources

- Lam Si Tung Ho, Cécile Ané, Asymptotic theory with hierarchical autocorrelation: Ornstein-Uhlenbeck tree models, arXiv:1306.1322 (2013). <https://doi.org/10.48550/arXiv.1306.1322>. Published version: The Annals of Statistics 41(2) (2013), 957–981, <https://doi.org/10.1214/13-aos1105>; locators above refer to the arXiv version.
