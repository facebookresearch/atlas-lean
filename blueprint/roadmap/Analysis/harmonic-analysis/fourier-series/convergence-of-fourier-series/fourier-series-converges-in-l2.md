# Fourier series of a square-integrable function converge in L²

Let $T > 0$ and let $\mu$ be the Haar measure normalized to be a probability measure on the circle $\mathbb{R}/T\mathbb{Z}$. For $n \in \mathbb{Z}$ write $e_n(t) = e^{2\pi i n t / T}$, and for $f \in L^2(\mathbb{R}/T\mathbb{Z}, \mu; \mathbb{C})$ write $\hat f(n) = \int e_{-n}(t)\, f(t)\, d\mu(t)$. Then the series $\sum_{n \in \mathbb{Z}} \hat f(n)\, e_n$ converges unconditionally (as a sum over $\mathbb{Z}$) to $f$ in the norm of $L^2(\mathbb{R}/T\mathbb{Z}, \mu; \mathbb{C})$; this is convergence in $L^2$, not pointwise.

Since $\mu$ has total mass $1$, $\hat f(n) = \frac{1}{T} \int_a^{a+T} e^{-2\pi i n t / T} f(t)\, dt$ for any real $a$. Together with the orthonormality of the $e_n$ in $L^2(\mu)$, this says that the functions $T^{-1/2} e^{2\pi i n t/T}$ form an orthonormal basis of $L^2([-\tfrac12 T, \tfrac12 T))$ with Lebesgue measure.

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 4.5.2, Theorem 4.14 (orthonormal basis from Fourier series, p. 383) and Theorem 4.15(i) ($L^2$ inversion, p. 384).
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842: `hasSum_fourier_series_L2`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/AddCircle.lean#L430-L434.
