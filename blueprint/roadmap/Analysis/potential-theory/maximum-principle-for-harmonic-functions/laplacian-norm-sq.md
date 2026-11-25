# Laplacian of the squared norm

Let $E$ be a real inner product space of finite dimension $n$. Then
$\Delta \|x\|^2 = 2n$ at every point. In $\mathbb{R}^n$ this is
$\Delta |x|^2 = \sum_i \partial_i^2 (x_1^2 + \dots + x_n^2) = 2n$.

The function $\varepsilon \|x\|^2$ is the perturbation that makes a subharmonic function strictly
subharmonic in the proof of the weak maximum principle.

## Informally uses

- [Second derivative along a line](iterated-fderiv-two-apply-eq-deriv-deriv.md): along the line
  $t \mapsto z + t e$ the function is the quadratic $\|z\|^2 + 2 t \langle z, e \rangle + t^2 \|e\|^2$,
  whose second derivative is $2 \|e\|^2$.

## Sources

- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, [Chapter 3 (Laplace equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_3.pdf), proof of Theorem 3.13, where the perturbation is $\exp(\alpha x_1)$ instead.
