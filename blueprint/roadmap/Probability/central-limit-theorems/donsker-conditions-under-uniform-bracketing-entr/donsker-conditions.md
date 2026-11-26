# Donsker conditions

Let $(\Omega, P)$ be a probability space, $\mu$ a measure on a measurable space $S$, $X_0, X_1, \dots : \Omega \to S$ maps, and $(F_i)_{i \in \iota}$ maps $S \to \mathbb{R}$; no measurability is assumed. Write $\mathbb{G}_n f = n^{-1/2} \sum_{k<n} (f(X_k) - \int f \, d\mu)$. The family satisfies the **Donsker conditions** if all three of the following hold.

1. Finite-dimensional convergence: for every $m \in \mathbb{N}$ and $i_0, \dots, i_{m-1} \in \iota$ there is a linear map $A : \mathbb{R}^m \to \mathbb{R}^m$ such that, for $Z \sim \mathcal{N}(0, I_m)$, $AZ$ is a Gaussian vector with $\langle AZ, t \rangle \sim \mathcal{N}(0, \mathrm{Var}_\mu[\sum_a t_a F_{i_a}])$ for every $t \in \mathbb{R}^m$, and $(\mathbb{G}_n F_{i_0}, \dots, \mathbb{G}_n F_{i_{m-1}})$ converges in distribution to $AZ$.
2. Total boundedness: for every $\delta > 0$ there is a finite $s \subseteq \iota$ such that every $i$ has some $j \in s$ with $\mathrm{Var}_\mu[F_i - F_j] < \delta^2$.
3. Asymptotic equicontinuity: for every $\varepsilon > 0$ and $\eta > 0$ there is $\delta > 0$ such that for all sufficiently large $n$,

$$P^*\Big( \exists\, i, j :\ \mathrm{Var}_\mu[F_i - F_j] < \delta^2 \ \text{and}\ \lvert \mathbb{G}_n F_i - \mathbb{G}_n F_j \rvert > \varepsilon \Big) \le \eta,$$

where $P^*$ is the outer measure of $P$.

Here $\mathrm{Var}_\mu[f]$ is the real part of the extended variance $\int (f - \int f \, d\mu)^2 \, d\mu \in [0, \infty]$, where $\int f \, d\mu$ is $0$ when $f$ is not integrable; it is $0$ when the extended variance is infinite. For a finite measure $\mu$ and an a.e. strongly measurable $f$ this means $\mathrm{Var}_\mu[f] = 0$ when $f \notin L^2(\mu)$. For an arbitrary map the value can differ: on two points with the trivial $\sigma$-algebra and a probability measure, the map with values $-1$ and $1$ is not a.e. measurable, its mean is $0$, its square is identically $1$, and its variance is $1$. When $\mu$ is a probability measure and $F_i, F_j \in L^2(\mu)$, $\mathrm{Var}_\mu[F_i - F_j]$ is the square of the standard-deviation semimetric $\rho_\mu(F_i, F_j) = \sqrt{\mathrm{Var}_\mu[F_i - F_j]}$.

## Sources

- A. W. van der Vaart and J. A. Wellner, *Weak Convergence and Empirical Processes*, Theorems 1.5.4 and 1.5.7 (see also §2.1.2), where for an i.i.d. sample these conditions are compared with the Donsker property.
