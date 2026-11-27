# Zero extension of a rectangular array to a product of cyclic groups

For natural numbers $M$, $K$, $N_1$ and $N_2$ and an array $x : \{0, \ldots, M-1\} \times \{0, \ldots, K-1\} \to \mathbb{C}$, the zero extension of $x$ to size $N_1 \times N_2$ is $x^{(N_1, N_2)} : \mathbb{Z}/N_1\mathbb{Z} \times \mathbb{Z}/N_2\mathbb{Z} \to \mathbb{C}$,

$$x^{(N_1, N_2)}(p_1, p_2) = \bar x(\operatorname{val} p_1, \operatorname{val} p_2),$$

where $\bar x$ is the [zero extension to pairs of natural numbers](extend-nat2.md), $\operatorname{val} i \in \{0, \ldots, N - 1\}$ is the least nonnegative representative of $i \in \mathbb{Z}/N\mathbb{Z}$, and $\operatorname{val} i = |i|$ on $\mathbb{Z}/0\mathbb{Z} = \mathbb{Z}$. It is the [one-dimensional zero extension](zero-extend.md) in each coordinate.

When $M \le N_1$ and $K \le N_2$ it keeps every entry and determines $x$ ([entries](zero-extend2-nat-cast.md), [injectivity](zero-extend2-injective.md)); for $N_1, N_2, M, K \ge 1$ the converse holds ([criterion](zero-extend2-injective-iff.md)), and a smaller size keeps only the leading entries. A zero size in a coordinate reads that coordinate back at its natural indices.
