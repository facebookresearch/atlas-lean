# Linear Gaussian channel: joint law and moments

Let $(\Omega, \mu)$ be a probability space and $\iota, \kappa$ nonempty finite index sets. Let $H \in \mathbb{R}^{\iota \times \kappa}$ and let $R \in \mathbb{R}^{\iota \times \iota}$ be positive definite. Let $X : \Omega \to \mathbb{R}^\kappa$ and $Z : \Omega \to \mathbb{R}^\iota$ be measurable and independent, with $Z \sim \mathcal{N}(0, R)$ and $\mathbb{E}\|X\|^2 < \infty$ (that is, $X \in L^2$). Let $m = \mathbb{E}[X]$ and let $K$ be the covariance matrix of $X$, $K_{ab} = \operatorname{Cov}(X_a, X_b)$. Set $Y = H X + Z$. Then:

1. the joint law of $(X, Y)$ is $\mathcal{L}(X) \otimes P$, the composition-product of the law of $X$ with the Markov kernel $P(x) = \mathcal{N}(H x, R)$, the law of $H x + Z$;
2. $Y \in L^2$;
3. $\mathbb{E}[Y] = H m$;
4. $\operatorname{Cov}(Y_i, Y_j) = (H K H^{\top} + R)_{ij}$ for all $i, j$;
5. $\operatorname{tr} K + \|m\|^2 = \mathbb{E}\|X\|^2$.
