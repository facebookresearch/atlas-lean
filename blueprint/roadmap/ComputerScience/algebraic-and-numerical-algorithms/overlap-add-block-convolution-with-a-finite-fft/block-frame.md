# Overlap-add block frame

Let $Q \ge 1$, $N$, $L$ and $M$ be natural numbers, $x$ a signal of length $N$, $h$ a kernel of length $M$ and $b \in \mathbb{N}$. The frame of block $b$ is $F_b : \mathbb{N} \to \mathbb{C}$,

$$F_b(t) = \begin{cases} \bigl((x^{[b]})^{(Q)} \circledast h^{(Q)}\bigr)(t \bmod Q) & t < Q, \\ 0 & t \ge Q, \end{cases}$$

where $x^{[b]}$ is [block $b$](block.md) of $x$ at hop $L$, $u^{(Q)}$ is the [zero extension](../support-bounded-zero-padding-for-cyclic-convolut/zero-extend.md) to length $Q$ and $\circledast$ is [cyclic convolution](../support-bounded-zero-padding-for-cyclic-convolut/cyclic-convolution.md) on $\mathbb{Z}/Q\mathbb{Z}$.
