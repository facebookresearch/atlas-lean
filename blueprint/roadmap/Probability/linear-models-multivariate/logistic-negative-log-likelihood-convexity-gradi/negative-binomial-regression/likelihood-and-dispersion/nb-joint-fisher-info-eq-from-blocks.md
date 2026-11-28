# The joint negative binomial Fisher information is block diagonal

For a shape $\theta$, design $X$, offset $o$ and coefficients $\beta$, the joint Fisher information is $\begin{pmatrix}X^\top\operatorname{diag}(F_i)X & 0\\ 0 & \sum_iv_{F,i}\end{pmatrix}$ with $F_i = \theta\mu_i/(\theta + \mu_i)$ and $v_{F,i}$ the Fisher shape information at $\eta_i = (X\beta)_i + o_i$.
