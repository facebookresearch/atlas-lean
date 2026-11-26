# Strong concavity of the CFN likelihood on a fixed tree

**Setting.** In the Cavender-Farris-Neyman (CFN) model, binary states $\sigma\in\{-1,+1\}$ evolve along a fixed unrooted binary tree $T=(V,E)$ with leaf set $L$: the root state is uniform and along each edge $e$ the state flips with probability $p_e\in(0,1/2)$, independently across edges. Equivalently each edge carries the correlation parameter $\theta_e=1-2p_e$, and the leaf configuration is a binary latent-tree (Ising) model. Given $m$ i.i.d. leaf configurations, the log-likelihood $\ell(\hat\theta)$ is maximized over $\hat\theta\in[-1,1]^E$ with the tree known. For a small parameter $\delta>0$ and fixed constants $C'>C>c>c'>0$ with $C'\ge2c'$, the **reconstruction regime** is

$$\Theta_0(\delta)=[1-2C\delta,\,1-2c\delta]^E\ \ni\theta^*,\qquad \hat\Theta_0(\delta)=[1-2C'\delta,\,1-2c'\delta]^E\ \ni\hat\theta,$$

so every true and candidate flip probability is of order $\delta$ and ancestral states can be reconstructed much better than at random. Let $\mathbf H(\hat\theta)$ be the Hessian of the population (expected, $m\to\infty$) log-likelihood.

**Theorem 1 and Corollary 2 (population landscape).** There are constants $\delta_0\in(0,1)$ and $0<C_1\le C_2$, depending only on $c,C,c',C'$ and not on the tree or its size, such that for every binary tree $T$, every $\delta\le\delta_0$, every $\theta^*\in\Theta_0(\delta)$ and every $\hat\theta\in\hat\Theta_0(\delta)$,

$$-\frac{C_2}{\delta}-26\ \le\ \lambda_{\min}(\mathbf H(\hat\theta))\ \le\ \lambda_{\max}(\mathbf H(\hat\theta))\ \le\ -\frac{C_1}{\delta}+26 .$$

Hence the population log-likelihood is $(C_1/\delta-26)$-strongly concave and $(C_2/\delta+26)$-smooth on $\hat\Theta_0(\delta)$, and $\theta^*$ is its unique maximizer there. Entrywise (Theorem 1), $-C_2/\delta\le\mathbf H_{e,e}\le-C_1/\delta$ and $\mathbf H_{e,f}\le(C_3\delta)^{\lfloor\max(\mathrm{dist}(e,f)-1,0)/4\rfloor}$ for edges $e\ne f$, so $\mathbf H$ is diagonally dominant.

**Theorems 3-5 (finite samples).** If $m\ge(C_4/\delta)^{\mathrm{diam}(T)+8}\log(1/\varepsilon)$, then with probability at least $1-\varepsilon$ the Hessian of the $m$-sample log-likelihood has all eigenvalues in $[-C_2/\delta-27,\,-C_1/\delta+27]$ uniformly over $\hat\Theta_0(\delta)$, its maximizer over $\hat\Theta_0(\delta)$ is close to $\theta^*$ in $\ell^\infty$, and coordinate maximization (optimizing one edge at a time) converges linearly to it from any start in $\hat\Theta_0(\delta)$.

## Expansion

The second derivative of the likelihood in $\theta_e$ involves the posterior agreement of the states at the two ends of $e$, computed by belief propagation from the two subtrees that $e$ separates. In the reconstruction regime the magnetization of each subtree's root given its leaves is robust to the exact parameter values (Theorem 11), so these conditional quantities are close to their values at $\theta^*$; the diagonal terms then behave like the Fisher information of a single binary channel with flip probability of order $\delta$, which is of order $1/\delta$. Off-diagonal entries couple edges through the path between them and decay geometrically in $\delta$ with tree distance; since a binary tree has at most exponentially many edges at a given distance, row sums of off-diagonal entries stay bounded for small $\delta$, uniformly in the tree. Diagonal dominance gives the eigenvalue bounds, and a uniform concentration argument over $\hat\Theta_0(\delta)$ transfers them to the empirical likelihood.

## Sources

- D. Clancy, H. Lyu, S. Roch, "Likelihood landscape of binary latent model on a tree", arXiv preprint (2025), Theorem 1, Corollary 2, Theorems 3-5, Theorem 11, <https://doi.org/10.48550/arXiv.2501.17622>.
