# Paley–Wiener theorem on a real vector space

This node is still to be broken down. It covers the Paley–Wiener theorem that the wave packets of Eisenstein series use.
Let $\mathfrak{a}$ be a finite-dimensional real vector space with a norm and a Haar measure, $\mathfrak{a}^*$ its dual with the dual
norm, $\mathfrak{a}^*_{\mathbb{C}}$ the complexified dual, and $E$ a finite-dimensional complex vector space.

- **Theorem** (Paley–Wiener). An entire function $\Psi \colon \mathfrak{a}^*_{\mathbb{C}} \to E$ is the Fourier–Laplace transform
  $\Psi(\lambda) = \int_{\mathfrak{a}} \psi(H) e^{-\lambda(H)} \, dH$ of a smooth function $\psi \colon \mathfrak{a} \to E$ supported in the closed ball
  of radius $R$ if and only if it is of Paley–Wiener type: for every $N$ there is $C_N$ with
  $\lVert \Psi(\lambda) \rVert \le C_N (1 + \lVert \lambda \rVert)^{-N} e^{R \lVert \operatorname{Re} \lambda \rVert}$, with the dual norm on $\mathfrak{a}^*$ and
  any norm on $\mathfrak{a}^*_{\mathbb{C}}$ for $\lVert \lambda \rVert$. The function $\psi$ is then
  recovered by integration of $\Psi(\lambda) e^{\lambda(H)}$ over any translate $\Lambda + i\mathfrak{a}^*$ of the imaginary subspace, with
  the dual measure.

## Expansion

A good expansion has a statement page for the theorem, in both directions, citing the sources below with locators. The case
$\Lambda = 0$ of the recovery of $\psi$ is Fourier inversion, after choosing an inner product on $\mathfrak{a}$, with Lebesgue measure $dV$
normalized by the unit cube on an orthonormal basis, and identifying $\xi \in \mathfrak{a}^*$ with $w \in \mathfrak{a}$ by
$\xi(H) = 2\pi \langle H, w \rangle$. If $dH = c \, dV$, then $\Psi(i\xi) = c \, \mathcal{F}\psi(w)$, where $\mathcal{F}$ is the Fourier transform for $dV$
with kernel $e^{-2\pi i \langle v, w \rangle}$, and the measure on $i\mathfrak{a}^*$ dual to $dH$ corresponds to $c^{-1} \, dV(w)$, so the two factors
cancel in $\psi(H) = \int_{i\mathfrak{a}^*} \Psi(\lambda) e^{\lambda(H)} \, d\lambda$. The converse direction needs $\mathcal{F}(\mathcal{F}^{-1} g) = g$ for the
function $g$ on $i\mathfrak{a}^*$ defined by the entire function, which follows from the same theorem by the reflection
$\mathcal{F}^{-1} g(v) = \mathcal{F} g(-v)$. The passage to $\Lambda + i\mathfrak{a}^*$, and the support estimate in the converse direction, are contour shifts,
one variable at a time, by Cauchy's theorem for rectangles and the growth estimate.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

- [Fourier inversion formula](fourier-inv-fourier-eq.md), for the recovery of $\psi$ from the values of $\Psi$ on the imaginary subspace $i\mathfrak{a}^*$, after the identification of $\mathfrak{a}$ with a Euclidean space and the rescaling by $2\pi$ described above, and, by reflection, for the inversion in the converse direction
- [Cauchy–Goursat theorem for rectangles](../../complex-analysis/cauchy-theory/contour-integrals-over-rectangles/boundary-integral-eq-zero.md), for the contour shifts from $i\mathfrak{a}^*$ to $\Lambda + i\mathfrak{a}^*$, one complex variable at a time, between which the growth estimate makes the horizontal sides vanish

## Sources

- L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Grundlehren 256, Springer, 1983, §7.3,
  Theorem 7.3.1 (the Paley–Wiener–Schwartz theorem).
- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §12, p. 65 (an entire function of $\lambda \in \mathfrak{a}^*_{P,\mathbb{C}}$ of Paley–Wiener type with values in a
  finite-dimensional space is the Fourier transform in $\lambda$ of a smooth compactly supported function on $\mathfrak{a}_P$, recovered
  by integration over $\Lambda + i\mathfrak{a}^*_P$).
