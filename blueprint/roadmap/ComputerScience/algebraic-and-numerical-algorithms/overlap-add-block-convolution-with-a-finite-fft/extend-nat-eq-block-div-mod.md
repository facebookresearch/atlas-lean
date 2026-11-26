# Every sample lies in exactly one block

Let $N$ and $L \ge 1$ be natural numbers and $x$ a signal of length $N$. For every $n \in \mathbb{N}$,

$$\bar x(n) = x^{[\lfloor n / L \rfloor]}_{n \bmod L},$$

where $\bar x$ is the [zero extension](../support-bounded-zero-padding-for-cyclic-convolut/extend-nat.md) of $x$ and $x^{[b]}$ is [block $b$](block.md): sample $n$ sits in block $\lfloor n / L \rfloor$ at offset $n \bmod L$.
