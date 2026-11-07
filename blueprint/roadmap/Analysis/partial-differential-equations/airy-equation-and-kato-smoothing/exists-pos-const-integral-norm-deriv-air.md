# Kato smoothing identity for the Airy equation

For $u_0 : \mathbb{R} \to \mathbb{C}$ let
$\widehat{u_0}(\xi) = (2\pi)^{-1/2} \int_{\mathbb{R}} u_0(y) e^{-iy\xi}\,dy$ be its unitary
Fourier transform, and let
$u(t, x) = (2\pi)^{-1/2} \int_{\mathbb{R}} e^{i(t\xi^3 + x\xi)}\, \widehat{u_0}(\xi)\,d\xi$ be
the Airy solution with initial datum $u_0$. There is a constant $c_0 > 0$ such that for every
smooth compactly supported $u_0 : \mathbb{R} \to \mathbb{C}$ and every $x_0 \in \mathbb{R}$, the
function $t \mapsto \partial_x u(t, x_0)$ belongs to $L^2(\mathbb{R})$ and

$$\int_{\mathbb{R}} |\partial_x u(t, x_0)|^2\,dt = c_0 \int_{\mathbb{R}} |u_0(x)|^2\,dx.$$

The source's formalization used the transform $\int u_0(y) e^{-2\pi i y\xi}\,dy$ together with
the unitary phase and prefactor, so its initial datum was not $u_0$ but the $L^2$-isometric
rescaling $x \mapsto (2\pi)^{-1/2} u_0(x / 2\pi)$; the identity holds for both with the same
$c_0$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Distributions, generalized functions, distribution spaces), `benchmark/level2/ma_proofbench_l2_27.lean` at openbmb/ma-proofbench@31bab4c, with the change above.
