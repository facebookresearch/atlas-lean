# Perturbed model-based planning attains the minimax rate for every accuracy

Planning in the empirical MDP with slightly randomly perturbed rewards finds, with probability at least $1-\delta$, an $\varepsilon$-optimal policy from $N \ge c_0\log(|S||A|/((1-\gamma)\varepsilon\delta))/((1-\gamma)^3\varepsilon^2)$ samples per state-action pair, for every $\varepsilon \in (0, 1/(1-\gamma)]$, removing earlier restrictions on the accuracy range.

**Setting.** Let $M = (S, A, P, r, \gamma)$ be a discounted MDP with finite state and action sets, rewards $r : S \times A \to [0, 1]$ and $\gamma \in (0, 1)$, and let $\hat P(s' \mid s, a) = \frac1N\sum_{i=1}^N \mathbf 1\{s^i_{s,a} = s'\}$ be the empirical transition probabilities of $N \ge 1$ samples per pair from [uniform sampling](generative-model-of-an-mdp.md). Perturb the rewards as

$$r_p(s, a) = r(s, a) + \zeta(s, a), \qquad \zeta(s, a) \overset{\text{i.i.d.}}{\sim} \mathrm{Unif}(0, \xi),$$

using no new samples, let $\hat M_p = (S, A, \hat P, r_p, \gamma)$ and let $\hat\pi^\star_p$ be the optimal policy of $\hat M_p$, maximizing its value $\hat V^\pi_p$.

**Theorem.** There exist universal constants $c_0, c_1 > 0$ such that for any $\delta > 0$ and any $0 < \varepsilon \le 1/(1-\gamma)$, with probability at least $1-\delta$ the policy $\hat\pi^\star_p$ satisfies, for all $(s, a) \in S \times A$,

$$V^{\hat\pi^\star_p}(s) \ge V^\star(s) - \varepsilon \quad\text{and}\quad Q^{\hat\pi^\star_p}(s, a) \ge Q^\star(s, a) - \gamma\varepsilon,$$

provided the perturbation size is $\xi = c_1(1-\gamma)\varepsilon/(|S|^5|A|^5)$ and

$$N \ge \frac{c_0\log\big(\frac{|S||A|}{(1-\gamma)\varepsilon\delta}\big)}{(1-\gamma)^3\varepsilon^2}.$$

In addition, empirical Q-value iteration recovers $\hat\pi^\star_p$ exactly within $O(\frac{1}{1-\gamma}\log\frac{|S||A|}{(1-\gamma)\varepsilon\delta})$ iterations. The result holds unchanged with $\xi = c_1(1-\gamma)\varepsilon/(|S|^\alpha|A|^\alpha)$ for any $\alpha \ge 1$. Combined with the generative-model lower bound, whose argument covers accuracies up to order $1/(1-\gamma)$, this makes the rate minimax optimal over the whole accuracy range; equivalently, the guarantee is non-trivial as soon as $N$ exceeds order $1/(1-\gamma)$ up to logarithms.

## Depends on

- [Generative model of an MDP](generative-model-of-an-mdp.md)
- [Value of a policy](../../../heuristic-search-and-planning/value-iteration/policy-value.md)
- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md)

## Proof depends on

- [Simulation lemma](../simulation-lemma/stoch-value-sub-stoch-value-eq.md)
- [Total-variance bound](total-variance-bound.md)
- [Bernstein's bound on the moment generating function of a bounded variable](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/mgf-le-of-abs-le.md)
- [Sums of independent sub-exponential variables](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/sum-of-i-indep-fun.md)
- [Sub-exponential tail bound, Gaussian regime](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/measure-real-ge-le-of-le.md)
- [Sub-exponential tail bound, exponential regime](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/measure-real-ge-le-of-ge.md)
- [Negation of a sub-exponential variable](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/neg.md)

## Expansion

Decompose $V^\star - V^{\hat\pi^\star} \le (\hat V^{\hat\pi^\star} - V^{\hat\pi^\star}) + (V^{\pi^\star} - \hat V^{\pi^\star})$ using the optimality of $\hat\pi^\star$ in the empirical model. For a fixed policy, the perturbation identity $\hat V^\pi - V^\pi = \gamma(I - \gamma\hat P_\pi)^{-1}(\hat P_\pi - P_\pi)V^\pi$ is expanded to logarithmic order in $1/(1-\gamma)$, and Bernstein bounds on each term, with the total-variance bound for the leading term, give, with the source's constants, $\|\hat V^\pi - V^\pi\|_\infty \le 6\sqrt{2\log(4|S|\log(e/(1-\gamma))/\delta)/(N(1-\gamma)^3)}$ whenever $N \ge (32e^2/(1-\gamma))\log(4|S|\log(e/(1-\gamma))/\delta)$; the same paper states this as a separate model-based policy-evaluation theorem. In the graph the Bernstein bounds come from a sub-exponential chain: centered samples bounded by $b$ with variance at most $\sigma^2$ are sub-exponential with parameters $(\sqrt2\sigma, 2b)$ by Bernstein's bound on the moment generating function (for $2b|t| < 1$ the factor $1/(1 - b|t|)$ is at most $2$), a sum of $n$ independent ones is sub-exponential with parameters $(\sqrt{2n}\sigma, 2b)$, and the two tail regimes, applied to the sum and to its negation, give for the average $\bar X$ and every $\ell > 0$ the one-sided bounds $\Pr(\pm\bar X \ge 2\sigma\sqrt{\ell/n} + 4b\ell/n) \le e^{-\ell}$. This changes the numerical constants $6$ and $32e^2$ but not the form of the bounds, and the theorem's universal constants $c_0$, $c_1$ absorb the change. For the data-dependent policy $\hat\pi^\star$, state-action-absorbing auxiliary MDPs, in which $(s, a)$ loops to itself with a designated reward $u$, are independent of the row $\hat P(\cdot \mid s, a)$, and when the empirical optimal action values are separated by a margin $\omega$ the optimal policy coincides with that of one auxiliary MDP on a finite grid of $u$. The random reward perturbation guarantees such a margin, of order $\xi\delta(1-\gamma)/(|S||A|^2)$, with probability $1-\delta$.

## Sources

- G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, "Breaking the Sample Size Barrier in Model-Based Reinforcement Learning with a Generative Model", *Advances in Neural Information Processing Systems* 33 (NeurIPS 2020), [proceedings.neurips.cc](https://proceedings.neurips.cc/paper/2020/hash/96ea64f3a1aa2fd00c72faacf0cb8ac9-Abstract.html): Section 2 (problem formulation), Theorem 1 with Remarks 1–2 and the following discussion, Theorem 2 (Section 3), and the proof outline with Lemmas 1–4 (Section 4).
