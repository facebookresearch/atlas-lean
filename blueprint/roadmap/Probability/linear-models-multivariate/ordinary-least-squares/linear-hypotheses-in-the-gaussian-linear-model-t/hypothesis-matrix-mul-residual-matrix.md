# The hypothesis matrix annihilates the residual maker

Let $X$ be a real $m \times k$ matrix and $C$ a real $r \times k$ matrix (a linear hypothesis $C\beta = c$ with $q = r$ restrictions), and let $B = (X^\top X)^{-1}X^\top$. The hypothesis matrix is $H_C = B^\top C^\top\big(C(X^\top X)^{-1}C^\top\big)^{-1}CB$ (matrix inverses, zero when singular). If $X^\top X$ is invertible, then $H_C M = 0$, where $M = I - X(X^\top X)^{-1}X^\top$ is the residual-maker matrix.
