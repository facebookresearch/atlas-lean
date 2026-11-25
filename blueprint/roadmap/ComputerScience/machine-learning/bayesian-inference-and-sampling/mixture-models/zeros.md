# Responsibility-weighted count of zeros

Let $\theta$ be valid parameters of a mixture of
$K$ products of $d$ Bernoulli distributions, let $x_0, \dots, x_{N-1} \in \{0,1\}^d$ be data, and
let $k < K$ be a component and $j < d$ a coordinate. Write $x_{nj}$ for the $j$-th coordinate of
$x_n$ and $r_k(x_n)$ for the responsibility of component $k$ for $x_n$ under $\theta$. The
weighted count is $\sum_{n < N,\ x_{nj} = 0} r_k(x_n)$, the sum of the responsibilities over the
points whose $j$-th coordinate is $0$.
