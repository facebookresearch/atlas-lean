# Fleming–Viot process with intrinsically varying population size

**Model.** Let $\mathbb{K}$ be a compact Polish type space. An *event* is $\bm z = (z_d, z_b) \in \mathcal{Z} = ([0,1]\times[0,\infty)) \setminus \{(0,0),(1,0)\}$: a fraction $z_d$ of the current population is killed and a mass $z_b$ of offspring of one parent is added. A *characteristic* $(\bm\gamma, \Pi)$ consists of a drift $\bm\gamma = (\gamma_d, \gamma_b) \ge \bm 0$ and a $\sigma$-finite measure $\Pi$ on $\mathcal{Z}$ satisfying the subordinator condition $\int_{\mathcal{Z}} \bm z\, d\Pi(\bm z) < \infty$ and the balance condition

$$\gamma_d + \int z_d\, d\Pi = \gamma_b + \int z_b\, d\Pi.$$

The $(\bm\gamma,\Pi)$-Fleming–Viot process is the $\mathcal{M}_F(\mathbb{K})$-valued solution $\sigma = N\rho$ ($N$ = population size, $\rho$ = type distribution) of the martingale problem for

$$\mathcal{L}F(N,\rho) = (\gamma_b - \gamma_d N)\,\partial_N F + \int_{\mathbb{K}}\int_{\mathcal{Z}} \Big[F\big((1-z_d)N + z_b,\, (1-\bar z)\rho + \bar z\,\delta_\kappa\big) - F(N,\rho)\Big]\, d\Pi(\bm z)\, d\rho(\kappa),$$

where $\bar z = z_b/((1-z_d)N + z_b)$ is the effective impact of the event at size $N$. The size process alone is Markov with generator $(\gamma_b - \gamma_d N)f'(N) + \int [f((1-z_d)N + z_b) - f(N)]\,d\Pi$.

**Theorem.**

1. *Well-posedness.* For every characteristic the martingale problem is well posed; the solution is a Hunt process and $N$ never hits $0$ or $\infty$ in finite time. $N$ is the strong solution of $dN_t = -N_{t-}\,dL^d_t + dL^b_t$ for a two-dimensional subordinator $(L^d, L^b)$ with drift $\bm\gamma$ and Lévy measure $\Pi$.
2. *Ergodicity of the size.* If $\gamma_d > 0$ and $\Pi \ne 0$, $N$ has a unique invariant law on $(0,\infty)$ with finite mean and converges to it exponentially fast in total variation from any integrable start.
3. *Closedness.* If $(\bm\gamma^{(n)}, \Pi^{(n)}) \to (\bm\gamma, \Pi)$ in the sense that $\bm\gamma^{(n)}\cdot\nabla g(\bm 0) + \int g\, d\Pi^{(n)} \to \bm\gamma\cdot\nabla g(\bm 0) + \int g\, d\Pi$ for all bounded continuous $g$ differentiable at $\bm 0$ with $g(\bm 0)=0$, then the processes converge weakly in Skorokhod space; no additional "zero-impact" (Wright–Fisher type) component arises in the limit.
4. *$\Lambda$-Fleming–Viot limit.* If $\Pi^{(n)}$ concentrates on the diagonal, $\int g\, d\Pi^{(n)} \to \int_0^1 g(u,u)\,u^{-2}\Lambda(du)$ for $g$ vanishing near $\bm 0$, and $\lim_{\epsilon\downarrow 0}\lim_n \int_{[0,\epsilon]^2}\big(z_b/(1-z_d+z_b)\big)^2 d\Pi^{(n)} = \Lambda(\{0\})$, then from $(N_0^{(n)}, \rho_0^{(n)}) \to (1, \rho_0)$ one gets $(N^{(n)}, \rho^{(n)}) \Rightarrow (1, \rho)$ with $\rho$ the $\Lambda$-Fleming–Viot process.

## Depends on

- [Infinite lookdown, de Finetti limit and the Λ-Fleming–Viot process](../../../../coalescent-theory/coalescents/infinite-lookdown-de-finetti-limit-and-lambda-fl.md)

## Expansion

Because births and deaths are balanced only in mean, small events can occur at rate of order $|\bm z|^{-1}$ (not $u^{-2}$ as for $\Lambda$-Fleming–Viot), which is exactly the subordinator condition; the size process is then a pathwise functional of a subordinator, giving existence and non-explosion. Given the size path, the type process is a $\Lambda$-Fleming–Viot process in a random environment, so a lookdown construction and a Markov-mapping argument give uniqueness. The $\Lambda$-Fleming–Viot limit arises when deaths and births of each event coincide, so $N \to 1$ and the effective impact becomes $u$.

## Sources

- Julian Kern and Bastian Wiederhold, "A Λ-Fleming-Viot type model with intrinsically varying population size", *Electronic Journal of Probability* 29 (2024), 1–28, <https://doi.org/10.1214/24-ejp1185>. Numbering as in the preprint arXiv:2311.06100v1, <https://arxiv.org/abs/2311.06100v1>: Section 2 (Definition 2.1, Theorems 2.3, 2.5 and 2.6 on well-posedness, closedness and convergence to the Λ-Fleming–Viot process), Section 3 (Proposition 3.3 on ergodicity of the population size).
