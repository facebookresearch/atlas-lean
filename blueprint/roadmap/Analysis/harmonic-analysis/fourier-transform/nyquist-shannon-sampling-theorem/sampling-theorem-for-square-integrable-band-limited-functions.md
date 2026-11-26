# Sampling theorem for square-integrable band-limited functions

Let $B > 0$ and $T > 0$ with $2BT \le 1$. For $g \in L^2([-B, B]; \mathbb{C})$ put

$$f_g(t) = \int_{-B}^{B} g(\xi)\, e^{2\pi i \xi t}\, d\xi \qquad (t \in \mathbb{R}),$$

a continuous function whose spectrum lies in $[-B, B]$. Write $\operatorname{sinc} u = \sin u / u$, with $\operatorname{sinc} 0 = 1$. Then:

1. **Sample norm.** $\sum_{n \in \mathbb{Z}} |f_g(nT)|^2 < \infty$, and $\int_{-B}^{B} |g(\xi)|^2\, d\xi = T \sum_{n \in \mathbb{Z}} |f_g(nT)|^2$.
2. **Injectivity.** If $f_{g_1}(nT) = f_{g_2}(nT)$ for every $n \in \mathbb{Z}$, then $g_1 = g_2$ almost everywhere, and $f_{g_1}(t) = f_{g_2}(t)$ for every $t$.
3. **Reconstruction.** For every $t \in \mathbb{R}$,

    $$f_g(t) = \sum_{n \in \mathbb{Z}} f_g(nT) \operatorname{sinc}\!\Big(\frac{\pi (t - nT)}{T}\Big),$$

    where the series converges absolutely, and the partial sums over $|n| \le N$ converge to $f_g$ uniformly on $\mathbb{R}$.

The critical rate $2BT = 1$ is included. If $x \in L^2(\mathbb{R})$ has a spectrum vanishing outside $[-B, B]$, then $x = f_g$ almost everywhere, with $g$ its spectrum; this is the band-limited class of the source's sampling theorem. A Schwartz function with spectrum in $[-\tfrac12, \tfrac12]$, sampled at $T = 1$, is the special case on the Nyquist–Shannon page.

**Proof.** Let $P = 1/T \ge 2B$. Extend $g$ by $0$ to $[-P/2, P/2)$ and regard it as an element $G$ of $L^2(\mathbb{R}/P\mathbb{Z})$ with the Haar probability measure. Its Fourier coefficients are $\hat G(n) = \frac{1}{P} \int_{-B}^{B} g(\xi) e^{-2\pi i n \xi / P}\, d\xi = T f_g(-nT)$.

- Parseval's identity gives part 1, and uniqueness of Fourier coefficients gives part 2.
- For part 3, the map $h \mapsto \int_{-P/2}^{P/2} h(\xi) e^{2\pi i \xi t}\, d\xi$ is continuous on $L^2$. Apply it to the $L^2$-convergent Fourier series of $G$, using $\int_{-P/2}^{P/2} e^{2\pi i n \xi / P} e^{2\pi i \xi t}\, d\xi = T^{-1} \operatorname{sinc}(\pi(t + nT)/T)$, and reindex $n \mapsto -n$.
- Parseval applied to $\xi \mapsto e^{2\pi i \xi t}$ on the period gives $\sum_n \operatorname{sinc}^2(\pi(t - nT)/T) = 1$. Absolute convergence then follows by Cauchy–Schwarz.
- The bound $|f_g(t) - s_N(t)| \le P^{1/2} \|G - G_N\|_{L^2([-P/2, P/2))}$, independent of $t$, gives uniform convergence; here $G_N$ is the partial Fourier sum of $G$ and $s_N$ the corresponding partial sum of the series.

## Proof depends on

- [Fourier series of a square-integrable function converge in L²](../../fourier-series/convergence-of-fourier-series/fourier-series-converges-in-l2.md): the $L^2$ expansion of the extended spectrum
- [Parseval's identity on the circle](../../fourier-series/convergence-of-fourier-series/parseval-identity-on-the-circle.md): the sample norm and $\sum_n \operatorname{sinc}^2 = 1$
- [Uniqueness of Fourier coefficients in L²](../../fourier-series/uniqueness-of-fourier-coefficients/eq-zero-of-fourier-coeff-eq-zero-lp.md): equal samples give equal Fourier coefficients, hence equal spectra

## Background

- [Nyquist–Shannon sampling theorem (Whittaker–Shannon interpolation formula)](nyquist-shannon-sampling.md): the case of Schwartz functions sampled at the Nyquist rate

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 5.4.2: Definitions 5.12 and 5.13 (bandwidth and the band-limited subspace, pp. 452–453), the orthonormality of the sinc shifts (p. 454), Theorem 5.14 (p. 454) and Theorem 5.15 (sampling theorem, p. 457); Section 4.5.2, Theorems 4.14 and 4.15 (the Fourier series of $L^2$ functions on an interval, pp. 383–384).
