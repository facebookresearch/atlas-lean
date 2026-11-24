# Correctness of the inverse FFT

Let $N = 2^d$, let $\omega \in \mathbb{C}$ be a primitive
$N$-th root of unity and let $x \in \mathbb{C}^N$. For every $k < N$, entry $k$ of the output of
the inverse FFT procedure on $x$ with root $\omega$ equals $N^{-1}$ times the discrete Fourier sum
of length $N$ with root $\overline{\omega}$ at frequency $k$ of the sequence $j \mapsto x_j$ (set
to $0$ for $j \ge N$), that is, $N^{-1} \sum_{j=0}^{N-1} \overline{\omega}^{jk} x_j$.
