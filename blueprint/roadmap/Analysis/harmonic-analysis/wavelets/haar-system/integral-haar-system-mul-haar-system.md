# Orthonormality of the Haar system

For all $j, k, j', k' \in \mathbb{Z}$,

$$\int_{\mathbb{R}} H_{j,k}(x)\, H_{j',k'}(x)\, dx = \begin{cases} 1 & (j, k) = (j', k'), \\ 0 & \text{otherwise,} \end{cases}$$

where $H_{j,k}(x) = 2^{j/2} H(2^j x - k)$: the Haar system is orthonormal in $L^2(\mathbb{R})$ (S. Mallat, *Multiresolution approximations and wavelet orthonormal bases of $L^2(\mathbb{R})$*, Trans. Amer. Math. Soc. 315 (1989), Section 4, after (70); R. A. DeVore, *Nonlinear approximation*, Acta Numerica 7 (1998), Section 3.5). Two Haar functions of the same scale and different translations have disjoint supports; at two different scales, the coarser function is constant on the dyadic interval supporting the finer one, which has [mean zero](integral-haar-function.md). The diagonal case is the [unit norm](integral-haar-function-sq.md) after the change of variables $y = 2^j x - k$. Completeness is the other half of the [Haar basis theorem](exists-hilbert-basis-haar-system.md).
