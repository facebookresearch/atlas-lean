# Nyquist–Shannon sampling theorem

For $W > 0$, a square-integrable signal whose spectrum is limited to the band $[-W, W]$ is determined by its samples at the points $n/2W$, and is recovered from them by the cardinal series $f(t) = \sum_n f(n/2W)\, \operatorname{sinc}(\pi(2Wt - n))$ (C. E. Shannon, *Communication in the presence of noise*, Proc. IRE 37 (1949), Theorem 1 and equation (7); E. T. Whittaker 1915). With the normalization $\hat f(\xi) = \int f(x)\, e^{-2\pi i x \xi}\, dx$ of the Fourier transform the Nyquist band for unit sampling is $[-\tfrac12, \tfrac12]$. The theorem is [stated](nyquist-shannon-sampling.md) for Schwartz functions: on the band the spectrum is [the Fourier series of the samples](fourier-eq-tsum.md), by Poisson's summation formula, and Fourier inversion integrates that series term by term.

- [The Fourier transform applied twice reflects](fourier-fourier-apply.md)
- [A band-limited spectrum is the Fourier series of the samples](fourier-eq-tsum.md)
- [Nyquist–Shannon sampling theorem (Whittaker–Shannon interpolation formula)](nyquist-shannon-sampling.md)

## Related topics

- [Wavelets and multiscale analysis](../../wavelets/README.md): the band-limited functions form the space $V_0$ of the Shannon multiresolution approximation, whose scaling function is the cardinal sine $\operatorname{sinc}(\pi t)$; wavelet bases replace the sharp frequency cut-off by localized filters.
- [Bernstein inequalities for band-limited functions](../bernstein-inequalities-for-band-limited-function/README.md): other properties of the same class of band-limited functions.
