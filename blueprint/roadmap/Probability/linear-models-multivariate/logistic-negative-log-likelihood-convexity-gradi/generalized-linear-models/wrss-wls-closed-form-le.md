# The closed form minimizes the weighted residual sum of squares

Let $X$ be an $m \times k$ real matrix, $w \in \mathbb{R}^m$ weights with $W = \operatorname{diag}(w)$ and $X^\top WX$ invertible, and $z \in \mathbb{R}^m$. If all weights are positive, then $b^* = (X^\top WX)^{-1}X^\top Wz$ satisfies $\sum_iw_i(z_i - (Xb^*)_i)^2 \le \sum_iw_i(z_i - (Xb)_i)^2$ for every $b$.
