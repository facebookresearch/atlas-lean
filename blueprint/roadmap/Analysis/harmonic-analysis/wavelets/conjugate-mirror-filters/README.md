# Conjugate mirror filters

One level of the fast wavelet transform filters a signal $x$ with a low-pass filter $h$ and a high-pass filter $g$ and keeps every other sample, $a[n] = \sum_k \overline{h[k - 2n]}\, x[k]$ and $d[n] = \sum_k \overline{g[k - 2n]}\, x[k]$; reconstruction upsamples and filters again (S. Mallat, *A theory for multiresolution signal decomposition: the wavelet representation*, IEEE Trans. Pattern Anal. Mach. Intell. 11 (1989), 674–693). In Mallat's *Multiresolution approximations and wavelet orthonormal bases of $L^2(\mathbb{R})$* (Trans. Amer. Math. Soc. 315 (1989), Section 4), the decomposition $a(\omega) = b(\omega)H(\omega) + c(\omega)G(\omega)$ of a $2\pi$-periodic function into $\pi$-periodic parts is orthogonal for every $a$ exactly when $|H(\omega)|^2 + |G(\omega)|^2 = 1$ and $H(\omega)\overline{G(\omega)} + H(\omega+\pi)\overline{G(\omega+\pi)} = 0$ (equation (66)); together with $|H(\omega)|^2 + |H(\omega+\pi)|^2 = 1$ this says that $\begin{pmatrix} H(\omega) & G(\omega) \\ H(\omega+\pi) & G(\omega+\pi)\end{pmatrix}$ is unitary (68), and $G(\omega) = e^{-i\omega}\overline{H(\omega+\pi)}$ is a possible choice (69).

The pages below give the finite, periodic version on $\mathbb{Z}/2N$: when the even translates of $h$ and $g$ are orthonormal, analysis followed by synthesis is the identity and preserves energy, and the mirror filter $g[k] = (-1)^{1-k}\,\overline{h[1-k]}$, the time-domain form of (69), completes any $h$ with orthonormal even translates.

- [Cyclic translate](shift.md)
- [Filtering and subsampling as an inner product](inner-shift-left.md)
- [Inner product of two translates](inner-shift-shift.md)
- [Atoms of the two-channel filter bank](filter-bank-atoms.md)
- [The atoms of an orthonormal filter bank form an orthonormal basis](filter-bank-basis.md)
- [Perfect reconstruction of the orthogonal two-channel filter bank](perfect-reconstruction.md)
- [Energy conservation of the orthogonal two-channel filter bank](norm-sq-eq-sum-add-sum.md)
- [Parity sign](parity-sign.md)
- [Mirror high-pass filter](mirror-filter.md)
- [Conjugate mirror filters give an orthonormal two-channel filter bank](orthonormal-filter-bank-atoms-mirror-fil.md)

## Related topics

- [Haar system](../haar-system/README.md): the Haar filters are the shortest conjugate mirror filters.
- [Convolution theorem for the discrete Fourier transform](../../discrete-fourier-analysis/inv-dft-mul-dft.md): filtering on $\mathbb{Z}/2N$ is circular convolution, which the discrete Fourier transform diagonalizes; in the frequency domain the conditions on $h$ and $g$ become Mallat's conditions (66)–(68) on $H$ and $G$.
- [Frames in Hilbert spaces](../../../hilbert-spaces/frames-in-hilbert-spaces/README.md): an orthonormal filter bank is a tight frame with bound $1$ whose atoms are also linearly independent; oversampled filter banks give redundant frames.
