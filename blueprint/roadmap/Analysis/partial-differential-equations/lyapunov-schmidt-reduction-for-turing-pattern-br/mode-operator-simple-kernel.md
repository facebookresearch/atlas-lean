# For f_v ≠ 0 and a simple critical mode, every package has kernel ℝφ

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $\iota$ be a finite set of modes with
real wavenumbers $\kappa_i$, let $d_u, d$ be real, and write $M_i = J - \kappa_i^2 D$ for the
[mode matrices](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md),
$D = \operatorname{diag}(d_u, d)$. Assume the mode $i_0$ is critical, $\det M_{i_0} = 0$, that
$f_v \neq 0$, and that no other mode is critical: $\det M_i \neq 0$ for $i \neq i_0$ (critical and
non-resonant: a simple critical mode). Let $\varphi$ be the [critical mode](critical-mode.md) of
$i_0$ and $\psi(y) = (M_{i_0})_{11}\, y_{i_0, 0} - f_v\, y_{i_0, 1}$ the
[critical functional](critical-functional.md). Then for every Fredholm package of the
[mode operator](mode-operator.md), with decompositions $X_1 \oplus X_0$ of the domain and
$Y_1 \oplus Y_0$ of the codomain:

- $\varphi \in X_0$, and every $z \in X_0$ is a real multiple of $\varphi$;
- $\psi$ vanishes on $Y_1$, the range of the mode operator;
- $\psi$ is injective on $Y_0$: $\psi(y) = 0$ with $y \in Y_0$ implies $y = 0$.

These are the hypotheses of the [reduction to a scalar equation](lyapunov-schmidt-scalar.md). Since
$\varphi \neq 0$ and $\psi \neq 0$, the kernel is one-dimensional and the range has codimension one,
so the index is zero.
