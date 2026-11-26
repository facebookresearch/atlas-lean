# Overlap-add frames by the discrete Fourier transform

Let $Q \ge 1$, $N$, $L$ and $M$ be natural numbers, $x$ a signal of length $N$, $h$ a kernel of length $M$, $b \in \mathbb{N}$ and $t < Q$. Then the [frame](block-frame.md) of block $b$ satisfies

$$F_b(t) = \mathcal{F}_Q^{-1}\bigl(\mathcal{F}_Q (x^{[b]})^{(Q)} \cdot \mathcal{F}_Q h^{(Q)}\bigr)(t \bmod Q),$$

where $x^{[b]}$ is [block $b$](block.md), $u^{(Q)}$ is the [zero extension](../support-bounded-zero-padding-for-cyclic-convolut/zero-extend.md) to length $Q$, the product is pointwise and $\mathcal{F}_Q$, $\mathcal{F}_Q^{-1}$ are the length-$Q$ discrete Fourier transform and its inverse, as in the [convolution theorem](../support-bounded-zero-padding-for-cyclic-convolut/cyclic-convolution-eq-inv-dft-mul.md).
