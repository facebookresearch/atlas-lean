# The log-likelihood is monotone along the EM iterates of a Bernoulli mixture

Let
$x_1, \dots, x_N \in \{0, 1\}^d$ be rich data: $N > 0$, and for every coordinate $j < d$ some
$x_n$ has $j$-th coordinate $1$ and some $x_m$ has $j$-th coordinate $0$. Let $\theta_0$ be valid
parameters of a mixture of $K$ products of $d$ Bernoulli distributions, and let $\theta_t$ be the
result of $t$ EM steps from $\theta_0$. Then $\ell(\theta_t)$ is nondecreasing in
$t \in \mathbb{N}$, where $\ell$ is the log-likelihood of the data under the mixture's joint
distribution.
