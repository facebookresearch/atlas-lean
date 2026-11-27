# Decoupled Bernstein bound for empirical optimal values

Although the empirical optimal value $\hat V^\star$ depends on the samples, the one-step error $(P - \hat P)\hat V^\star$ obeys a Bernstein-type bound with the variance of $\hat V^\star$ and a lower-order remainder, uniformly over state-action pairs. The proof uses absorbing-state MDPs on a grid of values.

Let $M$ be a discounted MDP with finite state and action sets, rewards in $[0, 1]$ and discount $\gamma \in (0, 1)$, and let $\hat M$ be the empirical MDP built from $N$ generative-model samples per state-action pair. Let $\pi^\star$ be an optimal policy of $M$ and $\hat V^{\pi^\star}$ its value in $\hat M$, and let $0 < \delta < 1$ and

$$L = \log\Big(\frac{8|S||A|}{(1-\gamma)\delta}\Big).$$

**Lemma.** With probability greater than $1-\delta$, entrywise on $S \times A$,

$$|(P - \hat P)\hat V^\star| \le \sqrt{\frac{8L}{N}}\sqrt{\mathrm{Var}_P(\hat V^\star)} + \Delta'_{\delta,N}\mathbf 1, \qquad |(P - \hat P)\hat V^{\pi^\star}| \le \sqrt{\frac{8L}{N}}\sqrt{\mathrm{Var}_P(\hat V^{\pi^\star})} + \Delta'_{\delta,N}\mathbf 1,$$

where

$$\Delta'_{\delta,N} = \sqrt{\frac{cL}{N}} + \frac{cL}{(1-\gamma)N}$$

for an absolute constant $c$.

## Depends on

- [Empirical MDP from a generative model](empirical-mdp-from-a-generative-model.md)

## Proof depends on

- [Absorbing-state MDP lemma](absorbing-state-mdp-lemma.md)
- [Bernstein's inequality for bounded variables, two-sided](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/measure-real-abs-ge-le-bernstein.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)
- [Simulation lemma](../simulation-lemma/stoch-value-sub-stoch-value-eq.md)

## Expansion

First, the simulation-lemma identity, Hoeffding's inequality and a union bound give the crude bound $\|Q^\star - \hat Q^\star\|_\infty \le \Delta_{\delta,N} = \frac{\gamma}{(1-\gamma)^2}\sqrt{2\log(2|S||A|/\delta)/N}$, so $\hat V^\star(s)$ lies in $[V^\star(s) - \Delta_{\delta/2,N}, V^\star(s) + \Delta_{\delta/2,N}]$ for all $s$ with probability $1 - \delta/2$. Cover this interval by a grid $U_s$ of $1/(1-\gamma)^2$ evenly spaced points. For each fixed $u \in U_s$, the row $\hat P(\cdot \mid s, a)$ is independent of $\hat V^\star_{s,u}$, so Bernstein's inequality and a union bound over $U_s$ give, with probability $1 - \delta$, for all $u \in U_s$

$$|(P - \hat P)(\cdot \mid s, a)\cdot\hat V^\star_{s,u}| \le \sqrt{\frac{2\log(4|U_s|/\delta)}{N}}\sqrt{\mathrm{Var}_{P(\cdot \mid s,a)}(\hat V^\star_{s,u})} + \frac{2\log(4|U_s|/\delta)}{3(1-\gamma)N}.$$

Since $\hat V^\star = \hat V^\star_{s,\hat V^\star(s)}$ and $\|\hat V^\star_{s,u} - \hat V^\star_{s,u'}\|_\infty \le |u - u'|$, replacing $\hat V^\star_{s,u}$ by $\hat V^\star$ costs $\min_{u \in U_s}|\hat V^\star(s) - u|$ times $1 + \sqrt{2\log(4|U_s|/\delta)/N}$, using $\sqrt{\mathrm{Var}(X+Y)} \le \sqrt{\mathrm{Var}(X)} + \sqrt{\mathrm{Var}(Y)}$; the grid spacing makes this a lower-order term. A union bound over the $|S||A|$ pairs gives the lemma, and the argument for $\hat V^{\pi^\star}$ is the same.

## Sources

- A. Agarwal, S. Kakade and L. F. Yang, "Model-Based Reinforcement Learning with a Generative Model is Minimax Optimal", *Proceedings of the Thirty Third Conference on Learning Theory*, PMLR 125 (2020), 67–83, [proceedings.mlr.press](https://proceedings.mlr.press/v125/agarwal20b.html): Lemma 11 with equation (3) and its proof, building on Lemma 6 (crude value bounds), Lemma 7 and Proposition 10 (Section 4.2).
