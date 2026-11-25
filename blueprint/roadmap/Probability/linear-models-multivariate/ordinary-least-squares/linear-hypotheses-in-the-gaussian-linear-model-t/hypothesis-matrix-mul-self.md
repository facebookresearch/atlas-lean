# The hypothesis matrix is idempotent

Let $X$ be a real $m \times k$ matrix and $C$ a real $r \times k$ matrix (a linear hypothesis $C\beta = c$ with $q = r$ restrictions), and let $B = (X^\top X)^{-1}X^\top$. The hypothesis matrix is $H_C = B^\top C^\top\big(C(X^\top X)^{-1}C^\top\big)^{-1}CB$ (matrix inverses, zero when singular). If $X^\top X$ and $C(X^\top X)^{-1}C^\top$ are invertible, then $H_C^2 = H_C$.
