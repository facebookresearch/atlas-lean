# Mixture of two stochastic policies

For $0 \le \alpha \le 1$ and stochastic policies $\pi, \pi'$, the mixture $\pi_\alpha = (1 - \alpha)\pi + \alpha \pi'$ takes action $a$ in state $s$ with probability $(1-\alpha)\pi(a \mid s) + \alpha \pi'(a \mid s)$. This is the conservative update of conservative policy iteration; deterministic policies are not closed under it.

## Sources

- S. Kakade, J. Langford, *Approximately Optimal Approximate Reinforcement Learning*, ICML 2002
- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Section 14.1.1
