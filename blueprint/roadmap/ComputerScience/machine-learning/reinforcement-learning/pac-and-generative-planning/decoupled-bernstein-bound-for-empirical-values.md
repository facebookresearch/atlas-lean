# Decoupled Bernstein bound for empirical optimal values

Although the empirical optimal value $\hat V^\star$ depends on the samples, with probability $1-\delta$ the one-step error $(P - \hat P)\hat V^\star$ obeys a Bernstein-type bound with the variance of $\hat V^\star$ and a lower-order remainder, uniformly over state-action pairs. The proof uses absorbing-state MDPs on a grid of values.

Let $M$ be a discounted MDP with finite state and action sets, rewards in $[0, 1]$ and discount $\gamma \in (0, 1)$, and let $\hat M$ be the empirical MDP, which keeps the rewards and the discount of $M$ and has transition probabilities $\hat P(s' \mid s, a) = \frac1N\sum_{i=1}^N \mathbf 1\{s^i_{s,a} = s'\}$ for the samples $s^i_{s,a}$ of [uniform sampling](generative-model-of-an-mdp.md), with $N \ge 1$; write $\hat V^\star$ for its optimal value. For $V : S \to \mathbb R$ write $(PV)(s, a) = \sum_{s'}P(s' \mid s, a)V(s')$ and $\mathrm{Var}_P(V) = P(V^2) - (PV)^2$, with squares, square roots and absolute values of vectors taken entrywise and $\mathbf 1$ the all-ones vector. Let $\pi^\star$ be an optimal policy of $M$ and $\hat V^{\pi^\star}$ its value in $\hat M$, and let $0 < \delta < 1$ and

$$L = \log\Big(\frac{8|S||A|}{(1-\gamma)\delta}\Big).$$

**Lemma.** With probability greater than $1-\delta$, entrywise on $S \times A$,

$$|(P - \hat P)\hat V^\star| \le \sqrt{\frac{8L}{N}}\sqrt{\mathrm{Var}_P(\hat V^\star)} + \Delta'_{\delta,N}\mathbf 1, \qquad |(P - \hat P)\hat V^{\pi^\star}| \le \sqrt{\frac{8L}{N}}\sqrt{\mathrm{Var}_P(\hat V^{\pi^\star})} + \Delta'_{\delta,N}\mathbf 1,$$

where

$$\Delta'_{\delta,N} = \sqrt{\frac{cL}{N}} + \frac{cL}{(1-\gamma)N}$$

for an absolute constant $c$.

## Depends on

- [Generative model of an MDP](generative-model-of-an-mdp.md)
- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md)
- [Value of a policy](../../../heuristic-search-and-planning/value-iteration/policy-value.md)

## Proof depends on

- [Absorbing-state MDP lemma](absorbing-state-mdp-lemma.md)
- [Bernstein's bound on the moment generating function of a bounded variable](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/mgf-le-of-abs-le.md)
- [Sums of independent sub-exponential variables](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/sum-of-i-indep-fun.md)
- [Sub-exponential tail bound, Gaussian regime](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/measure-real-ge-le-of-le.md)
- [Sub-exponential tail bound, exponential regime](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/measure-real-ge-le-of-ge.md)
- [Negation of a sub-exponential variable](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/neg.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)
- [Simulation lemma](../simulation-lemma/stoch-value-sub-stoch-value-eq.md)

## Expansion

The failure probability is split as $\delta/4$ for a crude bound and $\delta/4$ for the Bernstein events, so the total is $\delta/2 < \delta$.

*Crude bound.* The simulation-lemma identity, Hoeffding's inequality for the fixed vector $V^\star$ and a union bound over the pairs give, except with probability $\delta/4$, $\|Q^\star - \hat Q^\star\|_\infty \le \Delta := \frac{\gamma}{(1-\gamma)^2}\sqrt{2\log(8|S||A|/\delta)/N}$. The same event gives $\|Q^{\pi^\star} - \hat Q^{\pi^\star}\|_\infty \le \Delta$, since $V^{\pi^\star} = V^\star$. So $\hat V^\star(s)$ and $\hat V^{\pi^\star}(s)$ both lie in $I_s = [V^\star(s) - \Delta, V^\star(s) + \Delta] \cap [0, 1/(1-\gamma)]$ for every $s$.

*Grid.* Cover $I_s$ by a grid $U_s$ of evenly spaced points including its endpoints, with $|U_s| = \lceil 1/(1-\gamma)^2 \rceil + 1$; the spacing is $h \le 2\Delta(1-\gamma)^2 \le 2\sqrt{2L/N}$. The source takes $|U_s| = 1/(1-\gamma)^2$, which need not be an integer and is at least $2$ only when $\gamma \ge 1 - 1/\sqrt 2$.

*Bernstein events.* Fix $(s, a)$ and $u \in U_s$. The [absorbing-state MDP](absorbing-state-mdp-lemma.md) $\hat M_{s,u}$ is built from the samples at states other than $s$, so conditionally on those samples the variables $X_i = \hat V^\star_{s,u}(s^i_{s,a}) - (P\hat V^\star_{s,u})(s, a)$, $1 \le i \le N$, are independent and centered, with $|X_i| \le b = 1/(1-\gamma)$ (values lie in $[0, 1/(1-\gamma)]$ because $u$ does) and variance $\sigma^2 = \mathrm{Var}_{P(\cdot \mid s,a)}(\hat V^\star_{s,u})$. By Bernstein's bound on the moment generating function (for $2b|t| < 1$ the factor $1/(1 - b|t|)$ is at most $2$) each $X_i$ is sub-exponential with parameters $(\sqrt2\sigma, 2b)$. Their sum is sub-exponential with parameters $(\sqrt{2N}\sigma, 2b)$, and the Gaussian and exponential tail regimes, applied to the sum and to its negation, give for every $\ell > 0$

$$\Pr\Big(\pm(P - \hat P)(\cdot \mid s, a)\cdot\hat V^\star_{s,u} \ge 2\sigma\sqrt{\ell/N} + 4b\ell/N\Big) \le e^{-\ell}.$$

There are at most $4|S||A||U_s|$ such events (two signs, two value functions $\hat V^\star_{s,u}$ and $\hat V^{\pi^\star}_{s,u}$, the pairs and the grid). With $\ell = \log(16|S||A||U_s|/\delta)$ their total failure probability is at most $\delta/4$. Moreover $\ell \le 2L$. If $1/(1-\gamma)^2 \ge 2$, then $|U_s| \le 2/(1-\gamma)^2$, so $\ell \le \log(32|S||A|/\delta) + 2\log(1/(1-\gamma))$, and $\log(32|S||A|/\delta) \le 2\log(8|S||A|/\delta)$ because $\delta \le 2|S||A|$. Otherwise $|U_s| \le 3$, and $\ell \le \log(48|S||A|/\delta) \le 2\log(8|S||A|/\delta)$ because $\delta \le \frac43|S||A|$. Hence $2\sqrt{\ell/N}\,\sigma \le \sqrt{8L/N}\,\sigma$ and $4b\ell/N \le 8L/((1-\gamma)N)$.

*Transfer to $\hat V^\star$.* By the absorbing-state lemma $\hat V^\star = \hat V^\star_{s,\hat V^\star(s)}$ and $\|\hat V^\star_{s,u} - \hat V^\star_{s,u'}\|_\infty \le |u - u'|$. Take $u \in U_s$ nearest to $\hat V^\star(s)$, so the sup distance is at most $h$. By $\sqrt{\mathrm{Var}(X+Y)} \le \sqrt{\mathrm{Var}(X)} + \sqrt{\mathrm{Var}(Y)}$, the passage from $\hat V^\star_{s,u}$ to $\hat V^\star$ costs at most $2h + \sqrt{8L/N}\,h \le \sqrt{c L/N} + cL/((1-\gamma)N)$ for an absolute $c$, which together with $8L/((1-\gamma)N)$ gives $\Delta'_{\delta,N}$. The argument for $\hat V^{\pi^\star}$ is the same. So the stated constants $\sqrt{8L/N}$ and $\Delta'_{\delta,N}$ hold with probability at least $1 - \delta/2 > 1 - \delta$.

The source proves the Bernstein step with the sharp constants of Bernstein's inequality, $\sqrt{2\log(4|U_s|/\delta)/N}$ and $2\log(4|U_s|/\delta)/(3(1-\gamma)N)$ for each pair. The sub-exponential route above gives $2\sqrt{\ell/N}$ and $4\ell/((1-\gamma)N)$ instead, and the stated constants still follow.

## Sources

- A. Agarwal, S. Kakade and L. F. Yang, "Model-Based Reinforcement Learning with a Generative Model is Minimax Optimal", *Proceedings of the Thirty Third Conference on Learning Theory*, PMLR 125 (2020), 67–83, [proceedings.mlr.press](https://proceedings.mlr.press/v125/agarwal20b.html): Lemma 11 with equation (3) and its proof, building on Lemma 6 (crude value bounds), Lemma 7 and Proposition 10 (Section 4.2).
