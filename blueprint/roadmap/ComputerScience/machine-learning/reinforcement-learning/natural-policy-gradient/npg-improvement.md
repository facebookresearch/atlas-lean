# Improvement lower bound for natural policy gradient

Let $M$ be a Markov decision process with a finite set of states $S$, a finite nonempty set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. For a step size $\eta > 0$, the natural policy gradient iterates satisfy, for every $t$ and state $s_0$,

$$V^{\pi_{t+1}}(s_0) - V^{\pi_t}(s_0) \ge \frac{1-\gamma}{\eta} \log Z_t(s_0) \ge 0.$$

Here $Z_t(s) = \sum_a \pi_t(a \mid s) \exp\bigl(\eta A^{\pi_t}(s,a)/(1-\gamma)\bigr) = \exp\bigl(\operatorname{lse}_{\theta_{t+1}}(s) - \operatorname{lse}_{\theta_t}(s)\bigr)$. The published statement averages over a start distribution $\mu$; it follows by averaging.

## Sources

- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, Lemma 5.2
- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemma 12.8
