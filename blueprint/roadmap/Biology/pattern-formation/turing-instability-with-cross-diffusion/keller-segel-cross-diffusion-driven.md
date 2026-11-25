# Large χ destabilizes Keller–Segel, which no diagonal diffusion does

Let $r, \alpha, \beta, d_u, d_v > 0$, let
$\chi > (2 \sqrt{d_u d_v r \beta} + r d_v + \beta d_u)/\alpha$, and let
$J = \begin{pmatrix} -r & 0 \\ \alpha & -\beta \end{pmatrix}$ be the
[Keller–Segel Jacobian](keller-segel-jacobian.md) at $(1, \alpha/\beta)$. Then:

- for all $d_u', d_v' \ge 0$, no real wavenumber gives a
  [linearly unstable](../turing-patterns-and-diffusion-driven-instability/is-unstable-mode.md) mode
  of $J - k^2 \operatorname{diag}(d_u', d_v')$: no diagonal diffusion destabilizes the state;
- with the chemotactic [diffusion matrix](keller-segel-diffusion.md)
  $D = \begin{pmatrix} d_u & -\chi \\ 0 & d_v \end{pmatrix}$ (cell density $u_0 = 1$), some real
  wavenumber gives a [linearly unstable](is-cross-unstable-mode.md) mode.
