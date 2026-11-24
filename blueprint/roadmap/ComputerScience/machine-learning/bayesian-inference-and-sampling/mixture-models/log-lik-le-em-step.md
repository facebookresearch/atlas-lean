# Each EM step for the Bernoulli mixture does not decrease the log-likelihood

Let
$x_1, \dots, x_N \in \{0, 1\}^d$ be rich data: $N > 0$, and for every coordinate $j < d$ some
$x_n$ has $j$-th coordinate $1$ and some $x_m$ has $j$-th coordinate $0$. Let $\theta$ be valid
parameters of a mixture of $K$ products of $d$ Bernoulli distributions. Then
$\ell(\theta) \le \ell(\theta^+)$, where $\ell$ is the log-likelihood of the data under the
mixture's joint distribution and $\theta^+$ is the result of the EM step applied to $\theta$.
