# Fourier matrix acts as n times the inverse DFT

Let $n \ge 1$, let $\psi_n$ be the standard additive character of $\mathbb{Z}/n\mathbb{Z}$, and let
$\mathcal{F}$ be the discrete Fourier transform on functions
$\mathbb{Z}/n\mathbb{Z} \to \mathbb{C}$, $(\mathcal{F} v)(j) = \sum_k \psi_n(-kj)\, v(k)$, whose
inverse is $(\mathcal{F}^{-1} w)(k) = \frac{1}{n} \sum_j \psi_n(kj)\, w(j)$. Then for every
$v : \mathbb{Z}/n\mathbb{Z} \to \mathbb{C}$, the [Fourier matrix](fourier-matrix.md) satisfies
$F_n v = n\, \mathcal{F}^{-1} v$.
