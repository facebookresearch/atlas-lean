# Hitting property of expander walks

Let $G$ be a finite simple graph on $N$ vertices with adjacency matrix $A$, and let $d$ be a natural number and $\lambda$ a real number such that $G$ is a [spectral expander](is-spectral-expander.md) of degree $d$ with parameter $\lambda$: $G$ is $d$-regular, $\lambda \ge 0$ and $\lVert A x\rVert \le d \lambda \lVert x\rVert$ for every $x$ orthogonal to the constant vector, with $d \ge 1$ and $N \ge 1$. Let $B$ be a vertex set of density $\mu = \lvert B\rvert/N$ and $t$ a natural number. A [random walk](walk-prob.md) $V_0, V_1, \dots, V_t$ with $t$ steps from a uniformly random start vertex stays inside $B$ at all $t + 1$ times with probability at most

$$\big(\mu + \lambda(1 - \mu)\big)^{t + 1}$$

(S. Vadhan, *Pseudorandomness* (2012), Theorem 4.17, where the walk $V_1, \dots, V_t$ has $t - 1$ steps and the bound is $(\mu + \lambda(1 - \mu))^t$).

The proof follows Vadhan: the probability equals $\frac1N \mathbf 1^{\mathsf T} (P M)^t 1_B$, with $M = A/d$ and $P$ the projection onto $B$ (his Claim 4.20), and $\lVert P M y\rVert \le (\mu + \lambda(1 - \mu)) \lVert y\rVert$ for every $y$ supported on $B$ (his Claim 4.21), obtained by writing $M y = (1 - \lambda)\bar y \mathbf 1 + (\lambda \bar y \mathbf 1 + M y^\perp)$; the case $\lambda > 1$ is trivial because the bound is then at least $1$.

Taking $B$ the set of random strings on which a one-sided-error algorithm errs, a walk of $t$ steps uses $\log N + t \log d$ random bits, against $(t + 1)\log N$ for independent samples, and, when $\mu + \lambda(1 - \mu) < 1$ (for instance $\lambda < 1$ and $\mu < 1$), still drives the error down exponentially in $t$: error reduction for RP with few random bits.

## Background

- [Probability of an event for a random walk on a regular graph](walk-prob.md): the walk
  distribution used in the statement.
- [Bounded-error probabilistic classes RP and BPP](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/README.md):
  the hitting property is the tool for randomness-efficient error reduction of RP algorithms.
