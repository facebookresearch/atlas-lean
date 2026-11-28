# Weighted normal equations characterize the weighted least-squares estimate

Let $X$ be an $m \times k$ real matrix, $w \in \mathbb{R}^m$ weights with $W = \operatorname{diag}(w)$ and $X^\top WX$ invertible, and $z \in \mathbb{R}^m$. If all weights are nonzero, then $b$ solves $X^\top W(z - Xb) = 0$ if and only if $b = (X^\top WX)^{-1}X^\top Wz$.
