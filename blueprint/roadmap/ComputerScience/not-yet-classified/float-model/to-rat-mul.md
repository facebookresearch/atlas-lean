# Binary64 multiplication rounds the exact product in the normal range

Let $a$ and $b$ be binary64 floating-point values representing finite rationals $x$ and $y$. If $2^{-1022} \le |xy| \le (2^{53} - 1)\,2^{971}$, then the floating-point product $a \times b$ is finite and represents $\mathrm{fl}_{53}(xy)$, the rounding of $xy$ to 53 significant bits, to nearest with ties to even.
