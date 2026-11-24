# Inverse FFT after FFT is the identity at the negative-sign root

Let $N = 2^d$ and let
$\omega = e^{-2\pi i/N}$, the value at $-1$ of the standard additive character of
$\mathbb{Z}/N\mathbb{Z}$. For every $x \in \mathbb{C}^N$, running the FFT procedure on $x$ with
root $\omega$ and then the inverse FFT procedure on its output with root $\omega$ returns $x$.
