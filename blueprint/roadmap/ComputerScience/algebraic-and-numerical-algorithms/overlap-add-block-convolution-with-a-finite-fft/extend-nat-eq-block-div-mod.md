# Sample $n$ is entry $n \bmod L$ of block $\lfloor n/L \rfloor$

Let $N$ be a natural number, $L \ge 1$ a natural number, and $x$ a signal of length $N$. For every $n \in \mathbb{N}$,

$$\bar x(n) = x^{[\lfloor n / L \rfloor]}_{n \bmod L},$$

where $\bar x$ is the [zero extension](../support-bounded-zero-padding-for-cyclic-convolut/extend-nat.md) of $x$ and $x^{[b]}$ is [block $b$](block.md): sample $n$ sits in block $\lfloor n / L \rfloor$ at offset $n \bmod L$.
