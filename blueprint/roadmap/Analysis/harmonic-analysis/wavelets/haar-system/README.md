# Haar system

The [Haar function](haar-function.md) $H = \mathbf{1}_{[0,1/2)} - \mathbf{1}_{[1/2,1)}$ is the wavelet of the multiresolution approximation by piecewise constant functions on dyadic intervals, whose scaling function is $\mathbf{1}_{[0,1)}$ and whose filter is $H(\omega) = e^{-i\omega/2}\cos(\omega/2)$ (S. Mallat, *Multiresolution approximations and wavelet orthonormal bases of $L^2(\mathbb{R})$*, Trans. Amer. Math. Soc. 315 (1989), Section 4, after (70)). It has [mean zero](integral-haar-function.md), one vanishing moment, and [unit norm](integral-haar-function-sq.md). Its dilates and translates $H_{j,k}(x) = 2^{j/2} H(2^j x - k)$ form the [Haar system](haar-system.md), which is [orthonormal](integral-haar-system-mul-haar-system.md) and is an [orthonormal basis of $L^2(\mathbb{R})$](exists-hilbert-basis-haar-system.md); with the constant $1$, those supported in $[0,1)$ form an [orthonormal basis of $L^2[0,1)$](exists-hilbert-basis-haar-unit-interval.md) (R. A. DeVore, *Nonlinear approximation*, Acta Numerica 7 (1998), Section 3.5). The Haar multiresolution approximation is not regular: the Haar wavelet has a single vanishing moment and is discontinuous, so smooth functions have slowly decaying Haar coefficients.

- [Haar function](haar-function.md)
- [Haar system](haar-system.md)
- [The Haar function has mean zero](integral-haar-function.md)
- [The Haar function has unit $L^2$ norm](integral-haar-function-sq.md)
- [Orthonormality of the Haar system](integral-haar-system-mul-haar-system.md)
- [The Haar basis of $L^2[0,1)$](exists-hilbert-basis-haar-unit-interval.md)
- [The Haar wavelet basis of $L^2(\mathbb{R})$](exists-hilbert-basis-haar-system.md)

## Related topics

- [Conjugate mirror filters](../conjugate-mirror-filters/README.md): the Haar filters $h = (\delta_0 + \delta_1)/\sqrt2$ and $g = (\delta_0 - \delta_1)/\sqrt2$ are the simplest conjugate mirror filters; one level of the fast Haar transform maps $(x[2n], x[2n+1])$ to their normalized sum and difference.
- [Fourier analysis on the Boolean cube](../../discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/README.md): the Walsh functions, characters of $(\mathbb{Z}/2)^m$, and the first $m$ levels of the Haar basis are two orthonormal bases of the same space of step functions on the dyadic intervals of length $2^{-m}$; Walsh functions are localized in frequency, Haar functions in space.
- [Best M-term approximation](../../../approximation-theory/best-m-term-approximation/README.md): keeping the largest Haar coefficients is the best $M$-term approximation in the Haar basis, studied in DeVore's Section 3.6.
- [Multiresolution approximations](../multiresolution-approximations/README.md): the general framework of which the Haar system is the first example.
