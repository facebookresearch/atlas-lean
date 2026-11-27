# One Hestenes–Stiefel conjugate gradient step

Let $A$ be a real $n \times n$ matrix. One Hestenes–Stiefel conjugate gradient step maps a
[state](state.md) $(x, r, d)$ to $(x + \alpha d,\ r',\ r' + \beta d)$, where

$$\alpha = \frac{r^{\mathsf{T}} r}{d^{\mathsf{T}} A d}, \qquad r' = r - \alpha A d, \qquad
\beta = \frac{r'^{\mathsf{T}} r'}{r^{\mathsf{T}} r},$$

and a quotient with zero denominator is taken to be $0$.
