# Turing's criterion: infinitely many unstable k, finitely many k_n

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state) with $\operatorname{tr} J < 0$ and
$\det J > 0$, let $d_u, d_v > 0$ and $D = \operatorname{diag}(d_u, d_v)$, and assume
$2 \sqrt{d_u d_v \det J} < d_v f_u + d_u g_v$ (Turing's criterion). Then:

- infinitely many real wavenumbers $k$ are
  [linearly unstable](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode.md);
- for every $L > 0$, only finitely many Neumann modes $n$, with wavenumber $k_n = n\pi/L$, are
  unstable;
- there is $L_1 > 0$ such that for every $L$ with $0 < L \le L_1$ some real wavenumber is unstable
  while the homogeneous steady state is not [linearly unstable on $[0, L]$](is-neumann-unstable.md).
