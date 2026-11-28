# Big bang condition characterizes consistent ancestral state reconstruction

**Setting.** Let $(\mathbb{T}_n)_{n\ge1}$ be a nested sequence of rooted trees with known topology and edge lengths ($\mathbb{T}_n$ has $n$ leaves, all share the root, $\mathbb{T}_n \subseteq \mathbb{T}_{n+1}$) and uniformly bounded height $h^* = \sup_n \max_i t_i < \infty$, where $t_i$ is the root-to-leaf distance. For $s>0$ let $\mathbb{T}(s)$ be the tree truncated at distance $s$ from the root and $\partial\mathbb{T}(s)$ its leaf set (the cutset at time $s$). The sequence satisfies the **big bang condition** if

$$\lim_{n\to\infty} |\partial\mathbb{T}_n(s)| = \infty \quad \text{for every } s > 0.$$

A continuous trait evolves along the tree from root value $\rho$ by a time-homogeneous Markov process $Y$ on a state space $\mathcal{S}\subseteq\mathbb{R}$, independently on sister branches given the branch-point value; $P_{\rho,\mathbb{T}}$ is the law of the leaf values. Regularity conditions (all other model parameters known):

- $(A_1)$ there are continuous $u,v$ with $u>0$, a continuous injective $\phi:\mathcal{S}\to\mathbb{R}$ with continuous inverse, and a constant $C$ such that for $t\in[0,h^*]$

$$\mathbb{E}\{\phi[Y(t)]\mid Y(0)\} = u(t)\,\phi[Y(0)] + v(t), \qquad \operatorname{Var}\{\phi[Y(t)]\mid Y(0)\} \le C\,t;$$

- $(A_2)$ every $P_{\rho,\mathbb{T}}$ has a density, and for every tree there are $\rho_1\neq\rho_2$ whose leaf laws have nontrivially overlapping support ($\min\{P_{\rho_1,\mathbb{T}}(\mathcal{A}),P_{\rho_2,\mathbb{T}}(\mathcal{A})\}>0$ on the overlap $\mathcal{A}$).

An estimator $\hat\rho_n$ of the root state is **consistent** if $P_{\rho,\mathbb{T}_n}(|\hat\rho_n-\rho|>\epsilon)\to0$ for all $\epsilon>0$ and all $\rho$.

**Theorem.** Under $(A_1)$ and $(A_2)$, a consistent estimator of the ancestral state exists if and only if $(\mathbb{T}_n)$ satisfies the big bang condition. More precisely:

1. *(Necessity, needs only $(A_2)$.)* If $|\partial\mathbb{T}_n(s_0)| = K$ for some $s_0>0$ and all large $n$, then $d_{TV}(P_{\rho_1,\mathbb{T}_n},P_{\rho_2,\mathbb{T}_n}) \le d_{TV}(P_{\rho_1,\mathbb{T}_n(s_0)},P_{\rho_2,\mathbb{T}_n(s_0)}) \le C_0 < 1$ for all large $n$, so no estimator is consistent.
2. *(Sufficiency, needs only $(A_1)$.)* Under the big bang condition choose $n_k$ with $|\partial\mathbb{T}_{n_k}(1/k)|\ge k$ and a $k$-leaf subtree whose internal nodes are all within distance $1/k$ of the root, with leaf values $Y_{i,k}$ at depths $t_{i,k}$. Then

$$\hat\rho = \phi^{-1}\!\left(\frac1k\sum_{i=1}^k \frac{\phi(Y_{i,k}) - v(t_{i,k})}{u(t_{i,k})}\right)$$

is consistent.

## Proof sketch

Necessity: by the Markov property the leaves of $\mathbb{T}_n$ are a $\rho$-independent randomization of the values on the fixed $K$-leaf star $\mathbb{T}_n(s_0)$, and total variation cannot increase under a common Markov kernel; overlapping supports give $d_{TV} = 1 - \int f_{\rho_1}\wedge f_{\rho_2} < 1$, whereas a consistent estimator would force $d_{TV}\to1$. Sufficiency: the averaged statistic is unbiased for $\phi(\rho)$ by $(A_1)$. Each term has variance at most $Ch^*/m^2$ with $m = \min_{[0,h^*]}u$, and two leaves are conditionally independent given their most recent common ancestor at depth $t_{ij,k}\le 1/k$, so their covariance is $u(t_{ij,k})^2\operatorname{Var}\phi(Y_{ij,k}) \le M^2C/k$ with $M=\max_{[0,h^*]}u$. Hence the variance of the average is $O(1/k)$, Chebyshev gives convergence in probability, and the continuous $\phi^{-1}$ transfers it to $\hat\rho$. This extends the Brownian-motion and discrete-trait results, where the big bang condition was already known to be the exact criterion.

## Sources

- Nhat L. Vu, Thanh P. Nguyen, Binh T. Nguyen, Vu Dinh and Lam Si Tung Ho, "When can we reconstruct the ancestral state? Beyond Brownian motion", *Journal of Mathematical Biology* 86 (2023), 88, <https://doi.org/10.1007/s00285-023-01922-8>. Preprint version: arXiv:2207.12897 (2022), Definition 2.1, conditions $(A_1)$–$(A_2)$ (Section 2), Theorems 3.1, 3.2, 3.3, <https://doi.org/10.48550/arXiv.2207.12897>.
