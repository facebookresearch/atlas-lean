# Markov chain approximation of optimal harvesting and stocking under regime switching

**Model.** The population size $X(t) \ge 0$ lives in a random environment $\alpha(t)$, a continuous-time Markov chain on a finite set $\mathcal M = \{1,\dots,m_0\}$ with generator $Q = (q_{kl})$ (sudden environmental changes or catastrophes). A control $U(t) \in \mathcal U$, a compact interval containing both signs, harvests ($U > 0$) or stocks ($U < 0$):

$$dX(t) = \big[b(X(t), \alpha(t)) - U(t)\big]dt + \sigma(X(t), \alpha(t))\,dW(t).$$

With discount rate $\delta > 0$ and net revenue $p(x, \alpha, u)$ (harvesting income minus stocking cost), the value function is

$$V(x, \alpha) = \sup_{U}\, E_{x,\alpha}\int_0^\infty e^{-\delta s}\, p\big(X(s), \alpha(s), U(s)\big)\,ds,$$

the supremum over admissible (relaxed) controls. Formally $V$ solves the coupled Hamilton–Jacobi–Bellman system

$$\max_{u\in\mathcal U}\Big[V'(x,\alpha)\big(b(x,\alpha) - u\big) + \tfrac12\sigma^2(x,\alpha)V''(x,\alpha) + \sum_{k}q_{\alpha k}V(x,k) + p(x,\alpha,u) - \delta V(x,\alpha)\Big] = 0,$$

which under regime switching has no closed-form solution.

**Assumptions.** $b(\cdot,\alpha)$ and $\sigma(\cdot,\alpha)$ are locally Lipschitz, the uncontrolled equation has a unique global solution from every $(x,\alpha)$, and $p(\cdot,\alpha,\cdot)$ is bounded and continuous.

**Theorem.** Let $\{(X^h_n, \alpha^h_n)\}$ be a controlled Markov chain on a grid of mesh $h$ whose transition probabilities are locally consistent with the controlled diffusion (matching conditional mean and variance of increments to first order in the interpolation interval), with value function $V^h$. Then for every $(x,\alpha) \in \mathbb R_+ \times \mathcal M$,

$$V^h(x, \alpha) \to V(x, \alpha) \qquad (h \to 0),$$

so a near-optimal harvesting–stocking policy of the chain is near-optimal for the diffusion. The same convergence holds when the dynamics and prices are also periodic in time (seasonality), and when the population is coupled to an auxiliary environmental process with delay.

## Proof sketch

This is the Kushner–Dupuis Markov chain approximation method. Local consistency makes the piecewise-constant interpolations of the chain, together with relaxed controls, tight; every weak limit is a solution of the controlled switching diffusion under some relaxed control, and the interpolated switching process converges weakly to the Markov chain with generator $Q$. Upper and lower bounds then follow: $\limsup_h V^h \le V$ because limits of chain-optimal controls are admissible for the diffusion, and $\liminf_h V^h \ge V$ by approximating any $\varepsilon$-optimal diffusion control by piecewise-constant controls realizable on the chain. Numerically, the method shows how random switching and seasonality shift the optimal policy between harvesting and stocking regimes.

## Sources

- Alexandru Hening, Ky Quan Tran and Sergiu C. Ungureanu, "The effects of random and seasonal environmental fluctuations on optimal harvesting and stocking", *Journal of Mathematical Biology* 84 (2022), 41, <https://doi.org/10.1007/s00285-022-01750-2>. Preprint version: arXiv:2109.13169 (2021), standing assumptions, HJB equation, local consistency lemma and convergence theorems for the regime-switching, delayed and seasonal problems, <https://doi.org/10.48550/arXiv.2109.13169>.
