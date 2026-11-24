# Error bound when approximate policy iteration stops

Let $M$ be a Markov decision process with a finite set of states $S$, a finite nonempty set of actions, real rewards and stochastic transition probabilities, let $0 \le \gamma < 1$, and write $V^*$ for the optimal value, $V^\mu$ for the value of a deterministic policy $\mu$, $T$ for the Bellman optimality operator and $T_\mu$ for the Bellman operator of $\mu$. Suppose that $\bar J : S \to \mathbb{R}$ estimates the value of $\bar\mu$ to within $\delta$, that is $|\bar J(s) - V^{\bar\mu}(s)| \le \delta$ for every state $s$, and that $\bar\mu$ is greedy with respect to $\bar J$, that is $T_{\bar\mu} \bar J = T \bar J$ (approximate policy iteration has stopped at $\bar\mu$). Then for every state $s$

$$0 \le V^*(s) - V^{\bar\mu}(s) \le \frac{2\gamma\delta}{1-\gamma}.$$

The survey's proof (written there for costs) shows $T V^{\bar\mu} \le T \bar J + \gamma\delta = T_{\bar\mu} \bar J + \gamma\delta \le V^{\bar\mu} + 2\gamma\delta$ by monotonicity and the constant-shift property of $T$ and $T_{\bar\mu}$, applies $T$ repeatedly to get $T^m V^{\bar\mu} \le V^{\bar\mu} + 2\gamma\delta(1 + \gamma + \dots + \gamma^{m-1})$, and lets $m \to \infty$ by value iteration. The proof can end instead with the contraction of $T$: $\|V^* - V^{\bar\mu}\|_\infty \le \gamma \|V^* - V^{\bar\mu}\|_\infty + 2\gamma\delta$.

## Sources

- D. P. Bertsekas, *Approximate policy iteration: a survey and some new methods*, J. Control Theory Appl. 9(3) (2011), 310–335, Eq. (43) and the proof that follows it (stated there for costs, which are minimized).

## Informally uses

- [The Bellman optimality operator is monotone](../../../heuristic-search-and-planning/value-iteration/bellman-mono.md): the survey's proof applies $T$ to both sides of an inequality.
- [Value iteration converges](../../../heuristic-search-and-planning/value-iteration/tendsto-value-iteration.md): the survey's proof concludes with $V^* = \lim_m T^m V^{\bar\mu}$.

## Background

- [The Bellman operator contracts by γ](../../../heuristic-search-and-planning/value-iteration/abs-bellman-sub-le.md): the last step of the alternative proof, in place of the survey's limit argument.
