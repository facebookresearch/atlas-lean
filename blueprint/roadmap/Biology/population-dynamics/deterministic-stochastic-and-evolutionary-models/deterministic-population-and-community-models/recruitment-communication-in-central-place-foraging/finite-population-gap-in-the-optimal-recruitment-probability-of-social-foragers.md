# Finite-population gap in the optimal recruitment probability of social foragers

**Infinite-population model.** Foragers leave a central nest each round for one of $m$ sites. If a fraction $u_i$ goes to site $i$, a fraction $f_i(u_i)$ succeeds, with $f_i(0) = 0$, $f_i(x) < x$, $f_i' > 0$, $f_i'' < 0$ and $f_i(x) \to K_i < \infty$ (for example $f_i(x) = K_ix/(K_i + x)$, $K_i$ the resource abundance). Successful foragers return to their site; the unsuccessful fraction $1 - r_n$, $r_n = \sum_i f_i(u_{i,n})$, is recruited to site $i$ with probability $\rho f_i/r_n$ (communication, $\rho \in [0,1]$) or spreads uniformly with probability $(1-\rho)/m$:

$$\mathbf{u}_{n+1} = \mathbf{f}(\mathbf{u}_n) + \big(1 - \langle\mathbf{1}, \mathbf{f}(\mathbf{u}_n)\rangle\big)\Big(\frac{\rho\,\mathbf{f}(\mathbf{u}_n)}{\langle\mathbf{1}, \mathbf{f}(\mathbf{u}_n)\rangle} + \frac{1-\rho}{m}\mathbf{1}\Big), \qquad \langle\mathbf{1}, \mathbf{u}_n\rangle = 1.$$

The long-term reward rate is $\mu(\rho) = \lim_n r_n$.

**Finite-population model.** With $\xi$ foragers, $U_{i,n}$ fly to site $i$ and $V_{i,n} \sim \mathrm{Bin}\big(U_{i,n}, \phi_i(U_{i,n}/\xi)\big)$ succeed, where $f_i(x) = x\phi_i(x)$; unsuccessful foragers are reassigned with the same recruitment rule (uniformly if all fail). This is a finite Markov chain with a unique stationary distribution for every $\rho \in [0,1]$, and $\mu_\xi(\rho)$ is the stationary expected fraction of successful foragers.

**Results.**
1. For $0 \le \rho < 1$ the infinite-population map has a unique steady state. At $\rho = 1$ steady states satisfy the critical condition $\phi_i(u_i)^2 = z$ on the occupied sites of the constrained maximization of $\sum_i f_i(u_i)$, so $\rho^* = 1$ maximizes $\mu$ (uniquely unless resources are uniform, when $\mu$ does not depend on $\rho$): with infinitely many foragers, full communication is optimal.
2. For finite $\xi$ and $\rho = 1$, split the state space into the bulk $\mathcal{B}$ (every site occupied) and the edges $\mathcal{E}$ (some site empty). With $\alpha_* = 1/(1 + K_{\min})$, an upper bound on the per-forager failure probability, and $\beta_* = \min_{\mathbf{u}}\max_i G_i(\mathbf{u}) \in (\alpha_*, 1]$ over the simplex for explicit functions $G_i$, the stationary mass of the bulk satisfies $\|\pi_{\mathcal{B}}\|_1 \le 2(\alpha_*/\beta_*)^\xi \to 0$: the stationary distribution concentrates on edge states, in particular near the state with all foragers at the most abundant site, rather than near the ideal free allocation.
3. Consequently

$$\lim_{\xi\to\infty}\mu_\xi(1) < \lim_{\rho\to1}\mu(\rho),$$

so for every finite population an intermediate recruitment probability $\rho^* < 1$ is optimal, and $\mu_\xi$ has a boundary layer at $\rho = 1$ that sharpens as $\xi$ grows.

## Proof sketch

In the deterministic map, recruitment with $\rho < 1$ always reinjects a uniform share into every site, which forces a unique interior fixed point; as $\rho \uparrow 1$ the fixed point approaches the allocation that equalizes the marginal success $\phi_i^2$ across sites, which is the reward maximizer. With finitely many foragers and $\rho = 1$, demographic noise eventually empties sites, and an emptied site is never re-discovered because no forager is sent there at random; the chain gets trapped in quasi-stationary edge states with all foragers at one site, whose reward is strictly below the optimum. Any $\rho < 1$ restores exploration, so a small amount of non-communicated search pays off, however large the colony.

## Sources

- Hyunjoong Kim, Yoichiro Mori and Joshua B. Plotkin, "Finite Population Size Effects on Optimal Communication for Social Foragers", *SIAM Journal on Applied Mathematics* 84 (2024), 915–939, <https://doi.org/10.1137/23m1590007>. Preprint version: arXiv:2308.00298 (2023), Section 1.1 (summary of results), Section 2 (infinite-population model, uniqueness of the steady state for $\rho < 1$, long-term reward rate), Section 3 (finite-population Markov chain and its stationary distribution), Section 4 (quasi-steady states, the lemma $\alpha_* < \beta_*$, the proposition bounding $\|\pi_{\mathcal{B}}\|_1$, and existence of intermediate optimal recruitment), <https://doi.org/10.48550/arXiv.2308.00298>.
