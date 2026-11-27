# Transition matrix of a stochastic policy

For a Markov decision process with transition probabilities $P(s,a,s')$ and a stochastic policy $\pi$, the induced Markov chain has transition matrix $P^\pi(s, s') = \sum_a \pi(a \mid s)\, P(s, a, s')$.

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Section 1.1.2
