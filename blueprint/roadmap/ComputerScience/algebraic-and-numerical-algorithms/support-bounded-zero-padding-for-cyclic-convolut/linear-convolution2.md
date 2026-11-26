# Linear convolution of rectangular arrays

For natural numbers $M$, $K$, $P$ and $Q$, an $M \times K$ array $x$ and a $P \times Q$ array $y$, the linear convolution $x * y : \mathbb{N} \times \mathbb{N} \to \mathbb{C}$ is

$$(x * y)(t_1, t_2) = \sum_{i=0}^{t_1} \sum_{j=0}^{t_2} \bar x(i, j)\, \bar y(t_1 - i, t_2 - j),$$

where $\bar x$ and $\bar y$ are the [zero extensions](extend-nat2.md) to pairs of natural numbers.
