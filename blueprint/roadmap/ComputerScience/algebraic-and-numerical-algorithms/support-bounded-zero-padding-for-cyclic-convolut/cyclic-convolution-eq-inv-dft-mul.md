# Convolution theorem for zero-extended signals

Let $M$ and $K$ be natural numbers and $N \ge 1$ a natural number, and let $x$ and $y$ be signals of lengths $M$ and $K$, with [zero extensions](zero-extend.md) $x^{(N)}$ and $y^{(N)}$ to length $N$. Then

$$x^{(N)} \circledast y^{(N)} = \mathcal{F}_N^{-1}\bigl(\mathcal{F}_N x^{(N)} \cdot \mathcal{F}_N y^{(N)}\bigr),$$

where $\circledast$ is [cyclic convolution](cyclic-convolution.md), the product on the right is pointwise, and the length-$N$ discrete Fourier transform is $\mathcal{F}_N a(k) = \sum_{j \in \mathbb{Z}/N\mathbb{Z}} e^{-2\pi i\, \operatorname{val} j \operatorname{val} k / N}\, a(j)$, with inverse $\mathcal{F}_N^{-1} A(t) = \frac{1}{N} \sum_{k \in \mathbb{Z}/N\mathbb{Z}} e^{2\pi i\, \operatorname{val} k \operatorname{val} t / N}\, A(k)$. No relation between $M$, $K$ and $N$ is assumed.
