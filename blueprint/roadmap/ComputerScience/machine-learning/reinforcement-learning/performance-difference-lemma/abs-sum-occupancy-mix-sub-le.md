# Similar policies have similar occupancies

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. Let $0 \le \alpha \le 1$, let $\pi_\alpha = (1-\alpha)\pi + \alpha\pi'$, and let $|f(s)| \le C$ for all $s$. Then for every state $s_0$

$$\Bigl|\sum_s \bigl(d^{\pi_\alpha}_{s_0}(s) - d^\pi_{s_0}(s)\bigr) f(s)\Bigr| \le \frac{2\alpha\gamma C}{1-\gamma},$$

the dual form of $\|d^{\pi_\alpha}_{s_0} - d^\pi_{s_0}\|_1 \le 2\alpha\gamma/(1-\gamma)$.

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemma 14.1
