# Conservative policy iteration improves the policy

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. Let $0 \le \alpha \le 1$, let $\pi, \pi'$ be stochastic policies, let $\pi_\alpha = (1-\alpha)\pi + \alpha\pi'$, and suppose $\bigl|\sum_a \pi'(a \mid s) A^\pi(s,a)\bigr| \le \varepsilon$ for every state $s$. Then for every state $s_0$

$$V^{\pi_\alpha}(s_0) - V^\pi(s_0) \ge \frac{\alpha}{1-\gamma}\, \mathbb{A} - \frac{2\alpha^2\gamma\varepsilon}{(1-\gamma)^2},\qquad \mathbb{A} = \sum_s d^\pi_{s_0}(s) \sum_a \pi'(a \mid s)\, A^\pi(s,a).$$

When the policy advantage $\mathbb{A}$ is positive, a small enough step $\alpha$ improves the value: the gain is first order in $\alpha$ and the distribution-shift penalty second order. Kakade and Langford's Theorem 4.1 is sharper: it replaces one factor $1-\gamma$ of the penalty's denominator $(1-\gamma)^2$ by $1 - \gamma(1-\alpha)$.

## Sources

- S. Kakade, J. Langford, *Approximately Optimal Approximate Reinforcement Learning*, ICML 2002, Theorem 4.1
- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Theorem 14.2
