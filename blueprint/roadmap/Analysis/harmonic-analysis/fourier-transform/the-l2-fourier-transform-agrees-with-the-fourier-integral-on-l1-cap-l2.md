# The L² Fourier transform agrees with the Fourier integral on L¹ ∩ L²

For $f \in L^1(\mathbb{R})$ let $\hat f(\omega) = \int_{\mathbb{R}} f(t)\, e^{-i\omega t}\, dt$. Let $\mathcal{F} : L^2(\mathbb{R}) \to L^2(\mathbb{R})$ be the Fourier transform on square-integrable functions, the unique bounded linear operator with $\|\mathcal{F} f\|_2^2 = 2\pi\|f\|_2^2$ that extends the integral transform from a dense subspace of $L^2(\mathbb{R}) \cap L^1(\mathbb{R})$ (for example the Schwartz functions). Then for every $f \in L^1(\mathbb{R}) \cap L^2(\mathbb{R})$,

$$\mathcal{F} f = \hat f \quad \text{almost everywhere.}$$

In particular, for such $f$ the integral formula computes the $L^2$ transform pointwise, and $\hat f \in L^2(\mathbb{R})$ with $\|\hat f\|_2^2 = 2\pi\|f\|_2^2$.

## Expansion

The proof approximates $f \in L^1 \cap L^2$ by functions $f_n$ from the dense subspace converging to $f$ in both norms simultaneously, for example $f_n = f * \varphi_n$ truncated, with $\varphi_n$ an approximate identity. Convergence in $L^1$ gives $\hat f_n \to \hat f$ uniformly, convergence in $L^2$ gives $\mathcal{F} f_n \to \mathcal{F} f$ in $L^2$, and a subsequence converging almost everywhere identifies the two limits. The prerequisite is the $L^2$ Fourier transform on $\mathbb{R}$ itself: Plancherel's theorem, that the integral transform on the dense subspace is a multiple of an isometry and so extends uniquely.

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014, <https://www.fourierandwavelets.org/>, Section 4.4.2: the Fourier transform extended from $L^1(\mathbb{R})$ to $L^2(\mathbb{R})$, with the remark that a typical route uses the transform on $L^1(\mathbb{R}) \cap L^2(\mathbb{R})$ and the density of that space in $L^2(\mathbb{R})$ (p. 363 and footnote 85); Section 4.4.3, Parseval's equality (4.71a) for the Fourier transform, proved first on $L^1(\mathbb{R}) \cap L^2(\mathbb{R})$ and then extended (p. 371).
