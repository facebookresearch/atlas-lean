# Doob transform limit of time-inhomogeneous finite Markov chains conditioned to survive

**Setting.** Let $E$ be a finite set and $K$ a nonzero irreducible substochastic kernel on $E$ with killing ($\sum_y K(x,y) < 1$ for some $x$). By Perron–Frobenius, $K$ has an eigenvalue $\lambda \in (0,1)$ with positive left and right eigenvectors $L$, $R$, normalized by $LR = 1$. Its $h$-transform
$$Q(x,y) = \frac{R(y)K(x,y)}{\lambda R(x)}$$
is stochastic, with invariant law $\pi(x) = L(x)R(x)$, period $d$, cyclic classes $E_0,\dots,E_{d-1}$, and $\pi_r$ the restriction of $\pi$ to $E_r$, normalized.

Let $(K_n)_{n\ge0}$ be irreducible substochastic kernels with the same support as $K$ and, for some $N$,
$$\frac{K_n(x,y)}{K(x,y)} = 1 + \frac{a(x,y)}{n} + \frac{b(x,y)}{n^2} + O(n^{-3})\qquad (n \ge N),$$
uniformly in $x, y$. Let $\mathbb{P}_{(m,x)}$ be the law of the time-inhomogeneous chain with kernels $(K_n)$ started at $x$ at time $m$, with lifetime $\zeta$. Put $g(x) = \sum_y Q(x,y)a(x,y)$, $\kappa = \pi[g]$, and let $u$ solve the Poisson equation $(I - Q)u = g - \kappa$, $\pi[u] = 0$.

**Survival asymptotics.** There is $h : \mathbb{Z}_{\ge0}\times E \to (0,\infty)$ such that for $x \in E_r$,
$$\mathbb{P}_{(m,x)}(n < \zeta) = \pi_{r+n-m}\big[1/R\big]\,\lambda^{n-m}\,n^{\kappa}\,h(m,x)\,\big(1 + O(n^{-1})\big)\qquad (n \to \infty),$$
and $(m,x) \mapsto \lambda^{-m}h(m,x)$ is positive and space-time harmonic: $\sum_y K_m(x,y)h(m+1,y) = \lambda h(m,x)$.

**Conditioning limit.** For $k \ge m$ and any event $\Lambda_{m,k} \in \sigma(X_m,\dots,X_k)$,
$$\lim_{n\to\infty}\mathbb{P}_{(m,x)}(\Lambda_{m,k} \mid n < \zeta) = \mathbb{P}_{(m,x)}\Big[\mathbf{1}_{\Lambda_{m,k}}\,\lambda^{m-k}\,\frac{h(k,X_k)}{h(m,x)}\,\mathbf{1}_{\{k<\zeta\}}\Big],$$
so the chain conditioned on long survival is the Doob transform by $\lambda^{-m}h$, a time-inhomogeneous Markov chain with kernels $Q_n(x,y) = K_n(x,y)h(n+1,y)/(\lambda h(n,x))$.

**Behavior of the conditioned chain.**
- $Q_n(x,y) = Q(x,y)\big(1 + \frac{a(x,y) - \kappa + u(y) - u(x)}{n}\big) + O(n^{-2})$, and $Q_n = Q + O(n^{-2})$ iff $a(x,y) = \kappa + V(y) - V(x)$ on the support of $K$ for some $V : E \to \mathbb{R}$.
- $\|\mathbb{Q}_{(m,x)}(X_n \in \cdot) - \pi_{r+n-m}\|_{TV} = O(n^{-1})$, improving to $O(n^{-2})$ under the gradient condition above.
- Ergodic averages converge: $\frac1n\sum_{k=m}^{n-1}f(X_k) \to \pi[f]$ almost surely, so long-run occupation frequencies equal $\pi$.

## Expansion

The perturbation $a/n$ of the kernels changes the survival probability by a polynomial factor $n^{\kappa}$, with $\kappa$ the $\pi$-average of the first-order perturbation seen by the $h$-transformed chain. Writing the survival probability under $Q$ as a product of correction factors gives a positive martingale $W_{m,n}$ whose limit $W_{m,\infty}$ exists and is bounded above and below; $h$ is essentially $R$ times the expectation of $W_{m,\infty}$, and the conditioned law has density $W_{m,\infty}/\mathbf{Q}_{(m,x)}[W_{m,\infty}]$ with respect to the homogeneous transformed chain. When the perturbation is a gradient plus a constant it telescopes, which removes the first-order correction. Applications include Wright–Fisher and Moran models with time-varying selection conditioned on non-absorption, an elephant random walk confined to an interval, a generalized Pólya urn, and noncolliding random walks.

## Sources

- Kohki Iba, "Finite-State Time-Inhomogeneous Markov Chains Conditioned to Survive", arXiv:2610.38590 (2026), the two main theorems of Section 1.3 and Propositions 2.7 and 2.8 with the propositions and corollary of Section 2.2, <https://doi.org/10.48550/arXiv.2610.38590>.
