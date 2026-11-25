# The M-step of the Bernoulli mixture maximizes the EM objective

Let
$x_1, \dots, x_N \in \{0, 1\}^d$ be rich data: $N > 0$, and for every coordinate $j < d$ some
$x_n$ has $j$-th coordinate $1$ and some $x_m$ has $j$-th coordinate $0$. Let $\theta$ be valid
parameters of a mixture of $K$ products of $d$ Bernoulli distributions, and let $\theta^+$ be the
result of the EM step applied to $\theta$. Then every valid parameter $\theta'$ satisfies
$Q(\theta' \mid \theta) \le Q(\theta^+ \mid \theta)$, where $Q$ is the EM objective of the
mixture's joint distribution.
