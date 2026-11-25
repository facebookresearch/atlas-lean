# Discrete-time Fourier transform of square-summable sequences

Equip $\mathbb{R}/\mathbb{Z}$ with its Haar probability measure $d\nu$, and let $e_k(\nu) = e^{2\pi i k \nu}$ for $k \in \mathbb{Z}$. For $x \in \ell^2(\mathbb{Z}; \mathbb{C})$, the symmetric partial sums

$$X_N(\nu) = \sum_{|n| \le N} x_n\, e^{-2\pi i \nu n} = \sum_{|n| \le N} x_n\, e_{-n}(\nu)$$

converge in $L^2(\mathbb{R}/\mathbb{Z})$ as $N \to \infty$. Call the limit $\mathcal{F}x$, the discrete-time Fourier transform of $x$. Then:

1. **Isometric isomorphism.** $\mathcal{F} : \ell^2(\mathbb{Z}) \to L^2(\mathbb{R}/\mathbb{Z})$ is linear, bijective and isometric, $\|\mathcal{F}x\|_{L^2} = \|x\|_{\ell^2}$, and $\langle \mathcal{F}x, \mathcal{F}y \rangle = \sum_n x_n \overline{y_n}$, where $\langle f, g \rangle = \int f\, \overline{g}\, d\nu$.
2. **Coefficients and inversion.** For every $n$, the $n$-th Fourier coefficient of $\mathcal{F}x$ is $x_{-n}$, that is, $x_n = \int_0^1 (\mathcal{F}x)(\nu)\, e^{2\pi i \nu n}\, d\nu$. So $\mathcal{F}^{-1}$ sends $X \in L^2$ to the sequence $n \mapsto \hat X(-n)$.
3. **Agreement with the summable case.** If $x \in \ell^1(\mathbb{Z})$, then $\mathcal{F}x$ is the class of the continuous function $X(\nu) = \sum_n x_n e^{-2\pi i \nu n}$, the transform of absolutely summable sequences.

In angular frequency on $[-\pi, \pi)$ with Lebesgue measure, part 1 reads $\int_{-\pi}^{\pi} |X(e^{i\omega})|^2\, d\omega = 2\pi \sum_n |x_n|^2$, the source's Parseval equality, and $\mathcal{F}/\sqrt{2\pi}$ is unitary.

**Proof.**

- **Convergence and part 1.** The family $(e_k)_{k \in \mathbb{Z}}$ is orthonormal in $L^2(\mathbb{R}/\mathbb{Z})$, since $\int_0^1 e^{2\pi i (k - j)\nu}\, d\nu = \delta_{kj}$. So the partial sums are Cauchy whenever $\sum |x_n|^2 < \infty$, and $\|\mathcal{F}x\|^2 = \sum_n |x_n|^2$. Every $f \in L^2$ is the $L^2$ sum of its Fourier series, with square-summable coefficients, so $f = \mathcal{F}x$ for $x_n = \hat f(-n)$, and $\mathcal{F}$ is onto. Polarization gives the inner-product identity.
- **Part 2.** By orthonormality, $\langle \mathcal{F}x, e_n \rangle = x_{-n}$ for every $n$.
- **Part 3.** For $x \in \ell^1$ the partial sums converge uniformly to $X$, hence in $L^2$.

## Depends on

- [Discrete-time Fourier transform of absolutely summable sequences](discrete-time-fourier-transform-of-summable-sequences.md): the transform of absolutely summable sequences and its coefficient formula $\hat X(n) = x_{-n}$

## Proof depends on

- [Fourier series of a square-integrable function converge in L²](../fourier-series/convergence-of-fourier-series/fourier-series-converges-in-l2.md): every square-integrable function on the circle is the $L^2$ sum of its Fourier series
- [Parseval's identity on the circle](../fourier-series/convergence-of-fourier-series/parseval-identity-on-the-circle.md): the sum of the squared coefficient norms equals the squared $L^2$ norm

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 3.4.3: the DTFT as an operator $\ell^2(\mathbb{Z}) \to L^2([-\pi, \pi))$, the Parseval equality (3.107) (p. 226) and the unitarity of $\mathcal{F}/\sqrt{2\pi}$ (p. 226) and the adjoint $\mathcal{F}^* = 2\pi \mathcal{F}^{-1}$ (3.109) (p. 227).
