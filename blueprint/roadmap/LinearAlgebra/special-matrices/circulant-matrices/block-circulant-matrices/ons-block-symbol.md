# Fourier symbol of a block-circulant matrix

Let $n \ge 1$ and $d$ be natural numbers, let $\omega \in \mathbb{C}$, and let
$v : \mathbb{Z}/n\mathbb{Z} \to \mathbb{C}^{d \times d}$. The Fourier symbol of the
[block-circulant matrix](ons-block-circulant.md) of $v$ at the frequency
$j \in \mathbb{Z}/n\mathbb{Z}$ is the complex $d \times d$ matrix

$$\hat v(j) = \sum_{k \in \mathbb{Z}/n\mathbb{Z}} \omega^{kj}\, v(k),$$

where $k$ and $j$ are read as integers in $\{0, \dots, n-1\}$. In the determinant formula for
block-circulant matrices, $\omega$ is a primitive $n$-th root of unity.
