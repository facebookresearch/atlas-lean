# Fourier symbol of a two-dimensional block-circulant matrix

Let $L \ge 1$ and $d$ be natural numbers, let $\omega \in \mathbb{C}$, and let
$v : (\mathbb{Z}/L\mathbb{Z})^2 \to \mathbb{C}^{d \times d}$. The Fourier symbol of the
[two-dimensional block-circulant matrix](ons-block-circulant2-d.md) of $v$ at the frequency
$j = (j_1, j_2) \in (\mathbb{Z}/L\mathbb{Z})^2$ is the complex $d \times d$ matrix

$$\hat v(j) = \sum_{k \in (\mathbb{Z}/L\mathbb{Z})^2} \omega^{k_1 j_1 + k_2 j_2}\, v(k),$$

where the coordinates $k_1, k_2, j_1, j_2$ are read as integers in $\{0, \dots, L-1\}$. In the
determinant formula, $\omega$ is a primitive $L$-th root of unity.
