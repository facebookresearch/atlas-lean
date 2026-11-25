# Sinclair's Lemma 7

Let $P$ be a stochastic matrix, reversible with respect to a probability vector $\pi > 0$, and suppose $d_{TV}(P^t(x,\cdot), \pi) \le 1/4$ for every state $x$ and every $t \ge \tau$ (so $\tau$ is at least Sinclair's mixing time $\max_x \tau_x(1/4)$). Then for every $t \ge 2\tau$ and all states $x, y$,

$$P^t(x,y) \;\ge\; \pi(y)/8.$$

This is Lemma 7 of A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*, Combinatorics, Probability and Computing 1 (1992), 351–370, with its proof: the set $Z = \{z : P^\tau(y,z) \ge \pi(z)/2\}$ has $\pi(Z) \ge 1/2$, so $P^{t-\tau}(x, Z) \ge 1/4$; reversibility of $P^\tau$ gives $P^\tau(z,y) \ge \pi(y)/2$ on $Z$, and Chapman–Kolmogorov finishes. It is the step of Theorem 8 that turns mixing into positivity of every $t$-step transition probability.

## Background

- [Total variation distance of functions on a finite set](../mixing-times-of-markov-chains/tv-dist.md): the distance in the mixing hypothesis.
