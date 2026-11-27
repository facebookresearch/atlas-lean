# Correctness of the radix-two FFT

For every natural number $d$, every primitive $2^d$-th
root of unity $\omega \in \mathbb{C}$, every vector $x = (x_0, \dots, x_{2^d - 1})$ in
$\mathbb{C}^{2^d}$ and every $k < 2^d$, the $k$-th entry of the radix-two FFT of $x$ with root
$\omega$ equals the discrete Fourier sum $\sum_{j=0}^{2^d - 1} \omega^{jk} x_j$.
