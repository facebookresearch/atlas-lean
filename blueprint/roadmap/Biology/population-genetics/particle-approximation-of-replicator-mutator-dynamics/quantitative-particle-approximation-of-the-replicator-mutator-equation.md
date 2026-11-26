# Quantitative particle approximation of the replicator–mutator equation

**Replicator–mutator equation.** For a fitness (death) potential $V : \mathbb R^d \to [0,\infty)$ and mutation strength $\sigma > 0$, the density $\rho_t$ of traits in a large population evolves by

$$\partial_t\rho_t = \frac{\sigma^2}{2}\Delta\rho_t - \bigl(V - \mathbb E_{\rho_t}[V]\bigr)\rho_t ,$$

where the mean-fitness term keeps $\rho_t$ a probability measure. The diffusion models mutation and the source term models selection.

**Particle algorithm.** Fix $N$ particles $X_0^i \sim \rho_0$ i.i.d. and a step $\tau \in (0,1]$. At each step $n$, compute weights $w_n^i = e^{-\tau V(X_n^i)}/\sum_j e^{-\tau V(X_n^j)}$. Independently for each $i$, with probability $1 - e^{-\tau V(X_n^i)}$ the particle is killed and replaced by a copy of particle $J \sim \mathrm{Categorical}(w_n)$. Every particle then takes a Gaussian step: $X_{n+1}^i = X_n^{J} + \sigma\sqrt\tau\,\xi_n^i$ if it was replaced and $X_{n+1}^i = X_n^i + \sigma\sqrt\tau\,\xi_n^i$ otherwise, with $\xi_n^i \sim \mathcal N(0, I_d)$. Its mean-field limit is the splitting scheme $\rho_{n+1} = K_{\sigma\sqrt\tau} * \bigl(e^{-\tau V}\rho_n/\rho_n(e^{-\tau V})\bigr)$.

**Theorem.** Assume $V \in C^2(\mathbb R^d)$, $V \ge 0$, $V(x) \le C_V(1+|x|^2)$, $|\nabla V(x)| \le C'_V + V(x)$ and $|\Delta V(x)| \le C''_V(1+|x|^2)$. Let $\rho$ be a measure solution on $[0,T]$ with $\rho_0$ having finite moments of order $q \ge 4$, and let $\rho_n^N = \frac1N\sum_i\delta_{X_n^i}$. Then

$$\sup_{n\tau \le T}\mathbb E\bigl[\mathcal W_1^{d}\bigl(\rho_n^N, \rho(n\tau)\bigr)\bigr] \le C(1+T^2)\,e^{C(1+T^2)}\bigl(\varepsilon(N,d) + \tau\bigr),$$

where $\mathcal W^d_1$ is the Wasserstein-1 distance for the bounded cost $|x-y|\wedge 1$ (the bounded-Lipschitz distance), $C$ depends on $V, q, d$ and the $q$-th moment of $\rho_0$, and

$$\varepsilon(N,d) = \begin{cases} N^{-1/2}, & d = 1,\\ (1+\log N)\,N^{-1/2}, & d = 2,\\ N^{-1/d}, & d \ge 3.\end{cases}$$

So the particle system inherits the i.i.d. empirical-measure rate $\varepsilon(N,d)$ uniformly on $[0,T]$, plus a first-order time-discretization error. The dimension dependence already appears in the coupling between the interacting and the i.i.d. systems, because the resampling step does not average errors the way a mean-field drift does.

## Expansion

Couple the interacting particles with $N$ i.i.d. particles $\bar X_n^i \sim \rho_n$ driven by the same Gaussian noises and with resampling indices chosen through an optimal coupling of the weighted empirical measures. A one-step stability estimate for the reweighting map $\rho \mapsto e^{-\tau V}\rho/\rho(e^{-\tau V})$ in the bounded-Lipschitz metric, together with moment bounds that control the growth of $V$, gives $\mathbb E\,\mathcal W_1^d(\rho_n^N, \bar\rho_n^N) \lesssim_T \varepsilon(N,d)$ by a discrete Grönwall argument. Separately, the splitting scheme $\rho_n$ approximates the PDE solution to order $\tau$ in $\mathcal W_1^d$, using the bounds on $\nabla V$ and $\Delta V$. Fournier–Guillin concentration for $\bar\rho_n^N$ completes the estimate.

## Sources

- Giacomo Borghi, "Convergence of replicator-mutator particle systems via bounded Wasserstein distance", arXiv (2026). Section 1 (replicator–mutator PDE, Algorithm 1, Assumption on $V$, Theorem 1.2), Section 3 (Proposition 3.2), Section 4 (Definition 4.1, Proposition 4.2). <https://doi.org/10.48550/arXiv.2611.24472>
