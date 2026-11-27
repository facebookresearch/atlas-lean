# Hitting weight of first-passage step sequences

For a function $p : \mathbb{N} \to R$ with values in a commutative semiring $R$ and for
$k, n \in \mathbb{N}$, the hitting weight is

$$H_p(k, n) = \sum_{x} \prod_{i < n} p(x_i) ,$$

the sum over the $x \in \mathbb{N}^n$ with $x_0 + \dots + x_{n-1} + k = n$ that are [first-passage
sequences](is-first-passage.md): along them the walk started at $k$ with steps $x_i - 1$ first
hits $0$ at time $n$. For $p(j) = P(\xi = j)$, the offspring law of a Galton–Watson process, this
is the probability $P(T = n)$ that the total progeny of $k$ ancestors is $n$.
