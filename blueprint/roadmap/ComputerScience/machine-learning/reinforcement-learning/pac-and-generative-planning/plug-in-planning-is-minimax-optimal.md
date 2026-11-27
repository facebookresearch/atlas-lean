# Plug-in planning with a generative model is minimax optimal

Any near-optimal policy of the empirical MDP built from $N \ge c\gamma\log(|S||A|/((1-\gamma)\delta))/((1-\gamma)^3\varepsilon^2)$ samples per state-action pair is $\varepsilon$-optimal in the true MDP, up to its optimization error, for all $\varepsilon \in (0, (1-\gamma)^{-1/2}]$, with probability $1-\delta$.

**Setting.** Let $M = (S, A, P, r, \gamma)$ be a discounted MDP with finite state and action sets, a known deterministic reward $r \in [0, 1]$ and $\gamma \in (0, 1)$, and let $\hat M$ be the empirical MDP built from $N$ generative-model samples at every state-action pair. A deterministic stationary policy $\hat\pi$ is $\varepsilon_{\mathrm{opt}}$-optimal for $\hat M$ if $\|\hat Q^{\hat\pi} - \hat Q^\star\|_\infty \le \varepsilon_{\mathrm{opt}}$; it may be produced by any planner run on $\hat M$, such as value or policy iteration.

**Theorem.** Suppose $\delta > 0$ and $\varepsilon \in (0, (1-\gamma)^{-1/2}]$, and let $\hat\pi$ be any $\varepsilon_{\mathrm{opt}}$-optimal policy for $\hat M$. If

$$N \ge \frac{c\gamma\log\big(|S||A|(1-\gamma)^{-1}\delta^{-1}\big)}{(1-\gamma)^3\varepsilon^2},$$

then with probability at least $1-\delta$

$$Q^{\hat\pi} \ge Q^\star - \varepsilon - \frac{5\varepsilon_{\mathrm{opt}}}{1-\gamma}$$

entrywise, where $c$ is an absolute constant.

With $\varepsilon_{\mathrm{opt}}$ of order $(1-\gamma)\varepsilon$ this finds an $O(\varepsilon)$-optimal policy from $O(|S||A|\log(|S||A|/((1-\gamma)\delta))/((1-\gamma)^3\varepsilon^2))$ samples in total, which matches the lower bound for $\varepsilon \in (0, 1]$ up to a logarithmic factor. Earlier policy guarantees of this order for the plug-in approach required $\varepsilon$ below a threshold decreasing with $|S|$; perturbing the rewards extends the range to $\varepsilon \le 1/(1-\gamma)$.

## Depends on

- [Empirical MDP from a generative model](empirical-mdp-from-a-generative-model.md)
- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md)

## Proof depends on

- [Decoupled Bernstein bound for empirical optimal values](decoupled-bernstein-bound-for-empirical-values.md)
- [Total-variance bound](total-variance-bound.md)
- [Simulation lemma](../simulation-lemma/stoch-value-sub-stoch-value-eq.md)

## Expansion

For any policy $\pi$, $Q^\pi - \hat Q^\pi = \gamma(I - \gamma P^\pi)^{-1}(P - \hat P)\hat V^\pi$ (the simulation lemma with the roles of the two models exchanged), and

$$Q^{\hat\pi} \ge Q^\star - \|Q^{\hat\pi} - \hat Q^{\hat\pi}\|_\infty - \|\hat Q^{\hat\pi} - \hat Q^\star\|_\infty - \|\hat Q^{\pi^\star} - Q^\star\|_\infty.$$

The middle term is the optimization error. For the first, write $\hat V^{\hat\pi} = \hat V^\star + (\hat V^{\hat\pi} - \hat V^\star)$; the second part costs $2\gamma\varepsilon_{\mathrm{opt}}/(1-\gamma)$ by $\|(I - \gamma P^\pi)^{-1}\|_\infty \le 1/(1-\gamma)$, and the decoupled Bernstein bound controls $|(P - \hat P)\hat V^\star|$ by $\sqrt{8L/N}\sqrt{\mathrm{Var}_P(\hat V^\star)}$ plus a lower-order term. Splitting $\sqrt{\mathrm{Var}_P(\hat V^\star)}$ into $\sqrt{\mathrm{Var}_P(V^{\hat\pi})}$ and variances of differences, the total-variance bound gives $\sqrt{2/(1-\gamma)^3}$ for the main part, and the remaining part is a multiple of $\|Q^{\hat\pi} - \hat Q^{\hat\pi}\|_\infty$ with coefficient $\alpha_{\delta,N} = \frac{\gamma}{1-\gamma}\sqrt{8L/N} < 1/2$ under the sample condition, so the inequality can be solved for it. The third term is handled the same way with the fixed policy $\pi^\star$. The absorbing-state construction is what makes the analysis uniform over the data-dependent $\hat\pi$ without a union bound over all policies.

## Sources

- A. Agarwal, S. Kakade and L. F. Yang, "Model-Based Reinforcement Learning with a Generative Model is Minimax Optimal", *Proceedings of the Thirty Third Conference on Learning Theory*, PMLR 125 (2020), 67–83, [proceedings.mlr.press](https://proceedings.mlr.press/v125/agarwal20b.html): Section 2 (setting), Theorem 1 (Section 3) and its proof via Lemmas 3, 4, 5, 11 and 12 (Sections 4.1–4.3). The arXiv version arXiv:1906.03804v3 numbers the lemmas differently and states the theorem with $9\varepsilon_{\mathrm{opt}}/(1-\gamma)$ and $\gamma \ge 1/2$; the published constants are used here.
