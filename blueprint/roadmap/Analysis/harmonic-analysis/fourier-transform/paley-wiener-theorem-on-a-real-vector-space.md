# Paley–Wiener theorem on a real vector space

This node is still to be broken down. It covers the Paley–Wiener theorem that the wave packets of Eisenstein series use.
Let $\mathfrak{a}$ be a finite-dimensional real vector space with a norm and a Haar measure, $\mathfrak{a}^*_{\mathbb{C}}$ the complexified dual, and
$E$ a finite-dimensional complex vector space.

- **Theorem** (Paley–Wiener). An entire function $\Psi \colon \mathfrak{a}^*_{\mathbb{C}} \to E$ is the Fourier–Laplace transform
  $\Psi(\lambda) = \int_{\mathfrak{a}} \psi(H) e^{-\lambda(H)} \, dH$ of a smooth function $\psi \colon \mathfrak{a} \to E$ supported in the ball of
  radius $R$ if and only if it is of Paley–Wiener type: for every $N$ there is $C_N$ with
  $\lVert \Psi(\lambda) \rVert \le C_N (1 + \lVert \lambda \rVert)^{-N} e^{R \lVert \operatorname{Re} \lambda \rVert}$. The function $\psi$ is then
  recovered by integration of $\Psi(\lambda) e^{\lambda(H)}$ over any translate $\Lambda + i\mathfrak{a}^*$ of the imaginary subspace, with
  the dual measure.

## Expansion

A good expansion has a statement page for the theorem, in both directions, citing the sources below with locators; the
Fourier inversion along $\Lambda + i\mathfrak{a}^*$ follows from the case $\Lambda = 0$ by Cauchy's theorem and the growth estimate.

## Depends on

- [Fourier transform and uncertainty principles](README.md), for the Fourier transform on a real vector space

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Grundlehren 256, Springer, 1983, §7.3,
  Theorem 7.3.1 (the Paley–Wiener–Schwartz theorem).
- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §12, p. 65 (an entire function of $\lambda \in \mathfrak{a}^*_{P,\mathbb{C}}$ of Paley–Wiener type with values in a
  finite-dimensional space is the Fourier transform in $\lambda$ of a smooth compactly supported function on $\mathfrak{a}_P$, recovered
  by integration over $\Lambda + i\mathfrak{a}^*_P$).
