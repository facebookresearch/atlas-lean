# Inversion of the two-dimensional DFT sum

For $m, n \ge 1$ and every $x : \mathbb{Z}/m \times \mathbb{Z}/n \to \mathbb{C}$, let $X(k, l) = \sum_{i, j} e^{-2\pi i (ik/m + jl/n)}\, x(i, j)$ be its two-dimensional DFT sum, with $i, j, k, l$ read as their representatives in $\{0, \dots, m-1\}$ and $\{0, \dots, n-1\}$. Then

$$x(i, j) = \frac{1}{mn} \sum_{k, l} e^{2\pi i (ki/m + lj/n)}\, X(k, l).$$
