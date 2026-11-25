# Performance difference lemma for an initial distribution

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. For stochastic policies $\pi, \pi'$ and weights $\mu(s_0)$, with $V(\mu) = \sum_{s_0} \mu(s_0) V(s_0)$ and $d^{\pi'}_\mu(s) = \sum_{s_0} \mu(s_0) d^{\pi'}_{s_0}(s)$,

$$V^{\pi'}(\mu) - V^\pi(\mu) = \frac{1}{1-\gamma} \sum_s d^{\pi'}_\mu(s) \sum_a \pi'(a \mid s)\, A^\pi(s,a).$$

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemma 1.16
