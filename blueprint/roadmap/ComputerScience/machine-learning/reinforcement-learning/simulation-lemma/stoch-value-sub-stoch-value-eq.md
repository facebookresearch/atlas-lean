# Simulation lemma

Let $M$ and $\hat M$ be Markov decision processes on the same finite states $S$ and actions $A$, with the same rewards $r(s,a)$ and stochastic transition probabilities $P(s,a,s')$ and $\hat P(s,a,s')$, and let $0 \le \gamma < 1$. For every stochastic policy $\pi$, with $P^\pi$ and $\hat P^\pi$ the induced transition matrices,

$$V^\pi - \hat V^\pi = \gamma\,(I - \gamma \hat P^\pi)^{-1} (P^\pi - \hat P^\pi)\, V^\pi.$$

The value gap between a true and an estimated model is the effect of the one-step transition error, propagated through the estimated model. It is stated in the source for action values.

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemma 2.2
