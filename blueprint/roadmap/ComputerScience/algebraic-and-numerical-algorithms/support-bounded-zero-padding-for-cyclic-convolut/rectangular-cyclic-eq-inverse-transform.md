# Convolution theorem for zero-extended rectangular arrays

Let $M$, $K$, $P$ and $Q$ be natural numbers and $N_1 \ge 1$, $N_2 \ge 1$ natural numbers, $x$ an $M \times K$ array and $y$ a $P \times Q$ array, with [zero extensions](zero-extend2.md) $x^{(N_1, N_2)}$ and $y^{(N_1, N_2)}$. Then

$$x^{(N_1, N_2)} \circledast y^{(N_1, N_2)} = \mathcal{F}^{-1}\bigl(\mathcal{F} x^{(N_1, N_2)} \cdot \mathcal{F} y^{(N_1, N_2)}\bigr),$$

where $\circledast$ is cyclic convolution on $\mathbb{Z}/N_1\mathbb{Z} \times \mathbb{Z}/N_2\mathbb{Z}$ (as in [the padding bound for arrays](padded-cyclic-eq-linear-two-dim.md)), the product is pointwise, $\mathcal{F}$ applies the length-$N_2$ discrete Fourier transform along the second coordinate and then the length-$N_1$ transform along the first, and $\mathcal{F}^{-1}$ applies the inverse length-$N_1$ transform along the first coordinate and then the inverse length-$N_2$ transform along the second. The one-dimensional transforms are as in the [convolution theorem for signals](cyclic-convolution-eq-inv-dft-mul.md). No relation between the array sizes and $N_1, N_2$ is assumed.
