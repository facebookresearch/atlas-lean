# Mirror high-pass filter

For a low-pass filter $h$ on $\mathbb{Z}/2N$, the mirror high-pass filter is

$$g[k] = (-1)^{1-k}\, \overline{h[1-k]} .$$

If $H(\omega) = \sum_k h[k] e^{-ik\omega}$ and $G(\omega) = \sum_k g[k] e^{-ik\omega}$, then $G(\omega) = e^{-i\omega}\, \overline{H(\omega + \pi)}$, the choice (69) of S. Mallat, *Multiresolution approximations and wavelet orthonormal bases of $L^2(\mathbb{R})$*, Trans. Amer. Math. Soc. 315 (1989), Section 4.
