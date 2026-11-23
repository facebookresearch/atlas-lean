# The radix-two FFT with root $e^{2\pi i/n}$, divided by $n$, computes the inverse DFT

Let
$n = 2^d$ and let $x_0, \dots, x_{n-1}$ be complex numbers, indexed by $\mathbb{Z}/n\mathbb{Z}$.
Run the radix-two FFT on $x$ with sample root $\omega = e^{2\pi i/n}$, the value at $1$ of the
standard additive character of $\mathbb{Z}/n\mathbb{Z}$. Then for every $k < n$, entry $k$ of
the returned vector multiplied by $1/n$ equals the inverse discrete Fourier transform coefficient
$\frac{1}{n} \sum_{j \in \mathbb{Z}/n\mathbb{Z}} e^{2\pi i jk/n} x_j$.
