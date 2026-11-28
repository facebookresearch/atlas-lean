# Linear convolution of finite signals

For natural numbers $M$ and $K$ and signals $x : \{0, \ldots, M-1\} \to \mathbb{C}$ and $y : \{0, \ldots, K-1\} \to \mathbb{C}$, the linear convolution $x * y : \mathbb{N} \to \mathbb{C}$ is

$$(x * y)(t) = \sum_{j=0}^{t} \bar x(j)\, \bar y(t - j),$$

where $\bar x$ and $\bar y$ are the [zero extensions](extend-nat.md) of $x$ and $y$ to the natural numbers.
