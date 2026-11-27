# Estimating the shape does not change the coefficient information

For a shape $\theta$, design $X$, offset $o$ and coefficients $\beta$, if $A = X^\top\operatorname{diag}(F_i)X$ is invertible and the total shape information $D = \sum_iv_{F,i}$ is nonzero, then the inverse of the joint Fisher information is $\begin{pmatrix}A^{-1} & 0\\ 0 & D^{-1}\end{pmatrix}$.
