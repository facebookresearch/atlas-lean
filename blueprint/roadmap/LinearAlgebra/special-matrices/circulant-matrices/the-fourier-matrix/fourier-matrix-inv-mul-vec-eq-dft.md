# Inverse Fourier matrix acts as the DFT divided by n

Let $n \ge 1$, let $\psi_n$ be the standard additive character of $\mathbb{Z}/n\mathbb{Z}$, and let
$\mathcal{F}$ be the discrete Fourier transform, $(\mathcal{F} v)(j) = \sum_k \psi_n(-kj)\, v(k)$.
Then for every $v : \mathbb{Z}/n\mathbb{Z} \to \mathbb{C}$, the
[inverse Fourier matrix](fourier-matrix-inv.md) maps $v$ to $\frac{1}{n} \mathcal{F} v$.
