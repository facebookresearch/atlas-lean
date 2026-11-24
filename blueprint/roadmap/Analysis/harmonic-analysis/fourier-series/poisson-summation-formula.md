# Poisson summation formula for functions with power decay

Let $f \colon \mathbb{R} \to \mathbb{C}$ be continuous, with Fourier transform
$\hat{f}(\xi) = \int_{\mathbb{R}} f(t) \, e^{-2\pi i t \xi} \, dt$, and suppose that for some real $b > 1$ both
$f(t) = O(|t|^{-b})$ and $\hat{f}(\xi) = O(|\xi|^{-b})$ as $|t| \to \infty$ and $|\xi| \to \infty$. Then for every
$x \in \mathbb{R}$

$$\sum_{n \in \mathbb{Z}} f(x + n) = \sum_{n \in \mathbb{Z}} \hat{f}(n) \, e^{2\pi i n x}.$$

## Sources

- F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, Version 1.2.8 of 2026-09-15,
  <https://dlmf.nist.gov/1.8>, §1.8(iv), equation 1.8.14 (Poisson's summation formula, there for twice continuously
  differentiable $f$ with $f$ and $f''$ integrable).
- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf>, Chapter 1, §1, Proposition 2 and formula (7) (pp. 5–6), the Poisson
  summation formula in the form used for the Epstein zeta function.
