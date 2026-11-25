# Fourier eigenvalue of a circulant matrix

Let $n \ge 1$, let $\psi_n(k) = e^{2\pi i k/n}$ be the standard additive character of
$\mathbb{Z}/n\mathbb{Z}$, and let $v : \mathbb{Z}/n\mathbb{Z} \to \mathbb{C}$. The $j$-th Fourier
eigenvalue of the circulant matrix $C(v)$, whose entry in row $k$ and column $l$ is $v(k - l)$, is
the discrete Fourier transform of $v$ at $j \in \mathbb{Z}/n\mathbb{Z}$:

$$\lambda_j(v) = \sum_{k \in \mathbb{Z}/n\mathbb{Z}} \psi_n(-kj)\, v(k).$$
