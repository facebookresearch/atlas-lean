# The weighted least-squares estimate solves the normal equations

Let $X$ be an $m \times k$ real matrix, $w \in \mathbb{R}^m$ weights with $W = \operatorname{diag}(w)$ and $X^\top WX$ invertible, and $z \in \mathbb{R}^m$. If all weights are nonzero, then $b = (X^\top WX)^{-1}X^\top Wz$ satisfies $X^\top W(z - Xb) = 0$.
