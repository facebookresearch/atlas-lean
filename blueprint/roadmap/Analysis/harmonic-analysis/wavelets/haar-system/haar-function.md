# Haar function

The Haar function is

$$H(x) = \begin{cases} 1 & 0 \le x < 1/2, \\ -1 & 1/2 \le x < 1, \\ 0 & \text{otherwise,} \end{cases}$$

that is $H = \mathbf{1}_{[0,1/2)} - \mathbf{1}_{[1/2,1)}$ (R. A. DeVore, *Nonlinear approximation*, Acta Numerica 7 (1998), (3.40); S. Mallat, *Multiresolution approximations and wavelet orthonormal bases of $L^2(\mathbb{R})$*, Trans. Amer. Math. Soc. 315 (1989), Section 4, after (70)). It is the wavelet of the multiresolution approximation whose scaling function is $\mathbf{1}_{[0,1)}$: $H(x) = \mathbf{1}_{[0,1)}(2x) - \mathbf{1}_{[0,1)}(2x - 1)$.
