# Laplacian of the heat kernel

Let $E$ be a finite-dimensional real inner product space, $n = \dim E$, and let $\Phi$ be the [heat kernel](heat-kernel.md) on $E$. For $t > 0$ and $x \in E$,

$$\Delta_x \Phi(t, x) = \Phi(t, x) \left( \frac{\|x\|^2}{4 t^2} - \frac{n}{2 t} \right),$$

where $\Delta_x$ is the Laplacian of $\Phi(t, \cdot)$. Along each vector $e_i$ of an
orthonormal basis the second derivative is
$\Phi(t, x) \big( \langle x, e_i \rangle^2 / (4 t^2) - 1 / (2 t) \big)$, and
$\sum_i \langle x, e_i \rangle^2 = \|x\|^2$.

## Informally uses

- [Second derivative along a line](../../potential-theory/maximum-principle-for-harmonic-functions/iterated-fderiv-two-apply-eq-deriv-deriv.md):
  the second derivatives along the basis vectors are computed on lines.

## Sources

- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, [Chapter 4 (Heat equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf), §4.1.
- L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS Graduate Studies in Mathematics 19 (2010), Chapter 2. Not consulted directly; no theorem number is cited from it.
