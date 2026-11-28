# The BLUP prediction error does not depend on the fixed effects

Let $X$ ($n \times p$), $Z$ ($n \times q$), $G$ ($q \times q$) and $V$ ($n \times n$) be real matrices with $X^\top V^{-1}X$ invertible, and let $L = GZ^\top V^{-1}(I - X(X^\top V^{-1}X)^{-1}X^\top V^{-1})$ be the BLUP weight matrix. Then for all $\beta \in \mathbb{R}^p$, $u \in \mathbb{R}^q$ and $e \in \mathbb{R}^n$,

$$L(X\beta + Zu + e) - u = (LZ - I)u + Le.$$
