# The heat kernel solves the heat equation

Let $E$ be a finite-dimensional real inner product space and $\Phi$ the [heat kernel](heat-kernel.md) on $E$. For $t > 0$ and $x \in E$, the fundamental solution satisfies

$$\partial_t \Phi(t, x) = \Delta_x \Phi(t, x),$$

that is, $\Phi$ solves the heat equation $u_t - \Delta u = 0$ on $(0, \infty) \times E$, in every
finite dimension.

## Informally uses

- [Time derivative of the heat kernel](has-deriv-at-heat-kernel-time.md) and
  [Laplacian of the heat kernel](laplacian-heat-kernel.md): both sides equal
  $\Phi(t, x) (\|x\|^2 / (4 t^2) - n / (2 t))$.

## Sources

- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, [Chapter 4 (Heat equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf), §4.1 (the self-similar ansatz that produces $\Phi$ as a solution); the fact is used in the proof
  of Theorem 4.3 (ii), which concerns the convolution $\Phi * h$.
- L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS Graduate Studies in Mathematics 19 (2010), Chapter 2. Not consulted directly; no theorem number is cited from it.
