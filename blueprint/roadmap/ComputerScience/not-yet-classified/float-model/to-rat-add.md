# Binary64 addition rounds the exact sum in the normal range

Let $a$ and $b$ be finite binary64 values, with any encoding including subnormals and signed zeros, representing rationals $x$ and $y$. If $2^{-1022} \le |x + y| \le (2^{53} - 1)\,2^{971}$, then the binary64 sum $a + b$ represents $\mathrm{fl}_{53}(x + y)$, the rounding of $x + y$ to 53 significant bits, to nearest with ties to even.
