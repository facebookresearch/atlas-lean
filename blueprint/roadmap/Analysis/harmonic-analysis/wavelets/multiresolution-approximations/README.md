# Multiresolution approximations

A [multiresolution approximation](is-multiresolution-approximation.md) of $L^2(\mathbb{R})$ (S. Mallat, *Multiresolution approximations and wavelet orthonormal bases of $L^2(\mathbb{R})$*, Trans. Amer. Math. Soc. 315 (1989), 69–87) is a nested sequence of closed subspaces $V_j \subset V_{j+1}$, approximations at resolution $2^j$, invariant under dyadic dilation and translation, whose union is dense and whose intersection is $\{0\}$, and with $V_0$ isomorphic to $\ell^2(\mathbb{Z})$ compatibly with integer translations. Mallat proves that $V_0$ has an orthonormal basis of integer translates of one [scaling function](exists-scaling-function.md) $\varphi$, whose Fourier transform is determined by a $2\pi$-periodic filter $H$ with $\hat\varphi(2\omega) = H(\omega)\hat\varphi(\omega)$ and $|H(\omega)|^2 + |H(\omega + \pi)|^2 = 1$ (Theorem 1), and that the detail spaces $V_{j+1} \ominus V_j$ carry the dilated translates of a wavelet $\psi$, which together form a [wavelet orthonormal basis](exists-wavelet-hilbert-basis.md) of $L^2(\mathbb{R})$. The [Haar system](../haar-system/README.md) is the case $\varphi = \mathbf{1}_{[0,1)}$, and [conjugate mirror filters](../conjugate-mirror-filters/README.md) are the discrete side of the construction.

- [Multiresolution approximation of $L^2(\mathbb{R})$](is-multiresolution-approximation.md)
- [Scaling function of a multiresolution approximation](exists-scaling-function.md)
- [Wavelet orthonormal basis of a multiresolution approximation](exists-wavelet-hilbert-basis.md)

## Related topics

- [Haar system](../haar-system/README.md): the multiresolution approximation by step functions on dyadic intervals, with scaling function $\mathbf{1}_{[0,1)}$ and the Haar wavelet.
- [Conjugate mirror filters](../conjugate-mirror-filters/README.md): the filters $H$ and $G$ of the construction, and the perfect reconstruction of one level of the fast wavelet transform.
- [Riesz bases](../../../hilbert-spaces/riesz-bases/README.md): property (5) says that the integer translates of a function in $V_0$ can be taken to form a Riesz basis of $V_0$, which Mallat then orthonormalizes.
