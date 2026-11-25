# Conditional estimate as a fit to the first-block residual

For all real $n \times \iota_1$ and $n \times \iota_2$ matrices $X_1, X_2$ ($\iota_1, \iota_2$ finite sets) and $y \in \mathbb{R}^n$, the [conditional estimate](conditional-estimate.md) satisfies

$$\hat b_{2 \mid 1} = (X_2^\top X_2)^{-1} X_2^\top \bigl(y - X_1 (X_1^\top X_1)^{-1} X_1^\top y\bigr),$$

with the convention that the inverse of a singular matrix is $0$. When both Gram matrices are invertible, these are the successive least-squares fits on blocks 1 and 2. In general this is not the block-2 part of the joint estimate on both blocks; the two agree when both Gram matrices are invertible and $X_2^\top X_1 = 0$.
