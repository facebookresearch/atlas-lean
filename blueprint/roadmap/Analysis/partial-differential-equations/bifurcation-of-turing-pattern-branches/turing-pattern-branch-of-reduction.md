# Turing pattern branch from the Lyapunov–Schmidt reduction

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $\iota$ be a finite set of modes with
real wavenumbers $\kappa_i$, let $d_u$ be real, write $D(d) = \operatorname{diag}(d_u, d)$, and let
$i_0 \in \iota$ with $k = \kappa_{i_0}$. Assume:

- **critical mode:** $f_u k^2 - d_u k^4 > 0$ (admissible), $d_0 = d_n(k^2)$ is its
  [neutral diffusion](neutral-diffusion.md), $\operatorname{tr} J - k^2 (d_u + d_0) < 0$,
  $f_v \neq 0$, and no other mode is critical: $\det(J - \kappa_i^2 D(d_0)) \neq 0$ for
  $i \neq i_0$;
- **map:** $F$ maps (coefficient field, $d$) to coefficient fields, is strictly differentiable at
  $(0, d_0)$ with state derivative the
  [mode operator](../lyapunov-schmidt-reduction-for-turing-pattern-br/mode-operator.md) $L$ at
  $d_0$, has the trivial branch $F(0, d) = 0$ for $d$ near $d_0$, and for every $d$ near $d_0$ its
  state derivative at $0$ is the mode operator $w \mapsto ((J - \kappa_i^2 D(d))\, w_i)_i$;
- **reduction:** a Fredholm package of $L$ is fixed whose kernel part contains the
  [critical mode](../lyapunov-schmidt-reduction-for-turing-pattern-br/critical-mode.md) $\varphi$ at
  $d_0$, and $\tilde G(a, d) = a\, G(a, d)$ for $(a, d)$ near $(0, d_0)$, where $\tilde G$ is the
  [scalar bifurcation function](../lyapunov-schmidt-reduction-for-turing-pattern-br/ls-scalar.md)
  for $\varphi$ and the [normalized critical functional](normalized-critical-functional.md) at
  $d_0$, and $G$ is strictly differentiable at $(0, d_0)$ with derivative $G'$.

Let $W$ be the
[solution operator](../lyapunov-schmidt-reduction-for-turing-pattern-br/ls-solution.md) and
$\lambda_+$ the [leading real eigenvalue](leading-eigenvalue.md). Then:

- $\partial_d G(0, d_0) = G'(0, 1) = (d_u k^4 - f_u k^2)/(\operatorname{tr} J - k^2 (d_u + d_0))$,
  the crossing speed of the critical eigenvalue, and it is positive;
- for $d$ near $d_0$, $G(0, d)$ has the sign of $\lambda_+(J - k^2 D(d))$;
- there is $\beta : \mathbb{R} \to \mathbb{R}$ with $\beta(0) = d_0$, strictly differentiable at $0$
  with derivative $-G'(1, 0)/G'(0, 1)$, such that for $(w, d)$ near $(0, d_0)$, $F(w, d) = 0$ if and
  only if $w = 0$, or $w = a\varphi + W(a\varphi, d)$ and $d = \beta(a)$ for some $a$;
- for every $a \neq 0$ near $0$, the branch state $a\varphi + W(a\varphi, \beta(a))$ is a nonzero
  zero of $F(\cdot, \beta(a))$: a pattern;
- $G(0, d) < 0$ for $d < d_0$ and $G(0, d) > 0$ for $d > d_0$, for $d$ near $d_0$.

The values $G(0, d)$ are derived from the reduction, not assumed; they agree with the critical
eigenvalue to first order at $d_0$, and in general not beyond. Only the selected mode is controlled,
so nothing follows for the stability of the homogeneous state or of the branch.

In the model $d_u, d_0 > 0$; the statement holds for all real values.
