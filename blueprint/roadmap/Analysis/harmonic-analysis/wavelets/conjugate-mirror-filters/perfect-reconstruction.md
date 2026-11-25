# Perfect reconstruction of the orthogonal two-channel filter bank

Let $h, g$ be filters on $\mathbb{Z}/2N$ whose even translates $\tau_{2n} h, \tau_{2n} g$ ($0 \le n < N$) are orthonormal. Then every signal $x$ is recovered from its subsampled filter outputs $a[n] = \langle \tau_{2n} h, x\rangle$ and $d[n] = \langle \tau_{2n} g, x\rangle$:

$$x[k] = \sum_{n=0}^{N-1} a[n]\, h[k - 2n] + \sum_{n=0}^{N-1} d[n]\, g[k - 2n] .$$

This is the finite periodic form of the orthogonal decomposition $a(\omega) = b(\omega)H(\omega) + c(\omega)G(\omega)$ of S. Mallat, *Multiresolution approximations and wavelet orthonormal bases of $L^2(\mathbb{R})$*, Trans. Amer. Math. Soc. 315 (1989), Section 4, equations (65)–(68): synthesis is the adjoint of analysis, and analysis is an isometry onto $\mathbb{C}^{2N}$.
