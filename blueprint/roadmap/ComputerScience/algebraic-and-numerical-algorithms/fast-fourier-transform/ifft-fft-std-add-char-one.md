# Inverse FFT after FFT at the positive root is the identity

Let $d$ be a natural number,
$N = 2^d$ and $\omega = e^{2\pi i/N}$. For every vector $x \in \mathbb{C}^N$, running the
radix-two FFT with root $\omega$ on $x$ and then the inverse FFT with root $\omega$ on its output
returns $x$.
