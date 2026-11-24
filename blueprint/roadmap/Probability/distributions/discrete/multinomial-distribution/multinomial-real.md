# Multinomial mass function

Let $\iota$ be a finite set, $N \in \mathbb{N}$ and $p \in \mathbb{R}^\iota$. For a count vector
$x \in \mathbb{N}^\iota$, the multinomial mass function is

$$M_N(p; x) = \begin{cases} \dfrac{N!}{\prod_i x_i!} \displaystyle\prod_i p_i^{x_i} & \text{if } \sum_i x_i = N, \\ 0 & \text{otherwise.} \end{cases}$$

For a probability vector $p$ ($p_i \ge 0$, $\sum_i p_i = 1$) it is the probability that $N$
independent throws, landing in cell $i$ with probability $p_i$, produce the cell counts $x$. The
formula is a polynomial in $p$ and is defined for every real vector $p$. It can be a probability mass
function also when $p$ is not a probability vector: for $N = 0$ it is the point mass at the zero
vector for every $p$.
