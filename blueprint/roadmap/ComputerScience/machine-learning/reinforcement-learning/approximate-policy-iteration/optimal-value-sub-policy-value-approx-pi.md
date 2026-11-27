# Error bound for approximate policy iteration

Let $M$ be a Markov decision process with a finite set of states $S$, a finite nonempty set of actions, real rewards and stochastic transition probabilities, and let $0 \le \gamma < 1$. Let $\mu_0, \mu_1, \dots$ be deterministic policies and $J_0, J_1, \dots : S \to \mathbb{R}$ estimates of their values with $|J_k(s) - V^{\mu_k}(s)| \le \delta$ for all $k$ and $s$, and suppose that each $\mu_{k+1}$ is greedy with respect to $J_k$ ($T_{\mu_{k+1}} J_k = T J_k$). Then for all $k$ and every state $s$

$$V^*(s) - V^{\mu_k}(s) \le \gamma^k\, \|V^* - V^{\mu_0}\|_\infty + \frac{2\gamma\delta}{(1-\gamma)^2}.$$

The proof combines the one-step loss bound $V^{\mu_k} - V^{\mu_{k+1}} \le 2\gamma\delta/(1-\gamma)$ with the recursion $\|V^* - V^{\mu_{k+1}}\|_\infty \le \gamma \|V^* - V^{\mu_k}\|_\infty + 2\gamma\delta/(1-\gamma)$. Exact policy iteration is the case $\delta = 0$; the asymptotic form is [Asymptotic error bound for approximate policy iteration](limsup-dist-optimal-value-policy-value-l.md).

## Sources

- D. P. Bertsekas, *Approximate policy iteration: a survey and some new methods*, J. Control Theory Appl. 9(3) (2011), 310–335, Eq. (42). The survey states the bound in asymptotic form, for costs, and refers to earlier work for the proof; the non-asymptotic form with the transient $\gamma^k \|V^* - V^{\mu_0}\|_\infty$ is the form stated on this page.

## Background

- [Policy iteration terminates](../../../heuristic-search-and-planning/policy-iteration/policy-value-policy-iteration.md): exact policy iteration, the case $\delta = 0$, reaches an optimal policy after finitely many steps; with $\delta > 0$ only this asymptotic guarantee remains.
