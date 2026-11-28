# Ordered products of a time-varying matrix family

For a family $(A_k)_{k \in \mathbb{N}}$ of square matrices over a semiring, the ordered product is defined by recursion on the upper index: $\Phi(0, j) = I$, and $\Phi(k + 1, j) = I$ if $k + 1 \le j$, $\Phi(k + 1, j) = A_k\,\Phi(k, j)$ otherwise. So $\Phi(k, j) = A_{k-1}\cdots A_j$ for $j < k$ and $\Phi(k, j) = I$ for $j \ge k$.
