# Measure Mutual Information gaussian Input nondiagonal

Take $H = R = I_2$ and

$$K = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}.$$

For the input $X \sim \mathcal{N}(0, K)$ on $\mathbb{R}^2$ and output $X + Z$ with $Z \sim \mathcal{N}(0, I_2)$ independent of $X$, the mutual information of the joint law is $\frac{3}{2}$ bits; indeed $\det(I_2 + K) = 8$ and $\frac{1}{2}\log_2 8 = \frac{3}{2}$.
