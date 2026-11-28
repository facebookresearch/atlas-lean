# Finite-dimensional convergence

**Finite-dimensional convergence.** Let $(\Omega, P)$ be a probability space, $\mu$ a measure on a measurable space $S$, and $X_0, X_1, \dots : \Omega \to S$ mutually independent random variables, each with law $\mu$: almost everywhere measurable with pushforward $\mu$ under $P$, not necessarily measurable everywhere. $\mathbb{G}_n$ is the [empirical process](empirical-process.md), $0$ when $n = 0$. Let $(F_i)_{i \in \iota}$ be measurable functions $S \to \mathbb{R}$ in $L^2(\mu)$, and let $i_0, \dots, i_{m-1} \in \iota$. Write $\mathbb{G}_n f = n^{-1/2} \sum_{k<n} (f(X_k) - \int f \, d\mu)$. Then there is a linear map $A : \mathbb{R}^m \to \mathbb{R}^m$ such that, for $Z \sim \mathcal{N}(0, I_m)$:

- $AZ$ is a Gaussian vector, and for every $t \in \mathbb{R}^m$,

$$\langle AZ, t \rangle \sim \mathcal{N}\Big(0, \mathrm{Var}_\mu\Big[\sum_{a<m} t_a F_{i_a}\Big]\Big);$$

- the vectors $\big(\mathbb{G}_n F_{i_0}, \dots, \mathbb{G}_n F_{i_{m-1}}\big)$ converge in distribution to $AZ$ as $n \to \infty$.
