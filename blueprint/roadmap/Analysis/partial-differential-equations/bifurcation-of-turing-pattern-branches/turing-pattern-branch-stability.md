# Supercritical Turing branches are stable in the reduced equation

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $d_u$ and $k$ be real with
$f_u k^2 - d_u k^4 > 0$ (an admissible mode), let $d_0 = d_n(k^2)$ be its
[neutral diffusion](neutral-diffusion.md), assume $\operatorname{tr} J - k^2 (d_u + d_0) < 0$, and
write $D(d) = \operatorname{diag}(d_u, d)$. Let
$G, H, H_a : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ satisfy:

- $G$ is strictly differentiable at $(0, d_0)$, and $G(0, d) = \lambda_+(J - k^2 D(d))$ for $d$ near
  $d_0$, with $\lambda_+$ the [leading real eigenvalue](leading-eigenvalue.md);
- $G(a, d) = G(0, d) + a^2 H(a, d)$ for $(a, d)$ near $(0, d_0)$, with $H$ continuous at $(0, d_0)$
  and $c = H(0, d_0) \neq 0$;
- for $(a, d)$ near $(0, d_0)$, $x \mapsto H(x, d)$ has derivative $H_a(a, d)$ at $a$, and $H_a$ is
  continuous at $(0, d_0)$.

Then there is $\varphi : \mathbb{R} \to \mathbb{R}$ with $\varphi(0) = d_0$ such that:

- near $(0, d_0)$, $a\, G(a, d) = 0$ if and only if $a = 0$ or $d = \varphi(a)$;
- $G(0, d) < 0$ for $d < d_0$ and $G(0, d) > 0$ for $d > d_0$, for $d$ near $d_0$;
- for every $a \neq 0$ close enough to $0$, $c\,(\varphi(a) - d_0) < 0$, and
  $x \mapsto x\, G(x, \varphi(a))$ has a derivative $\lambda$ at $a$ with $c\, \lambda > 0$.

In particular, if $c < 0$ the branch lies in $d > d_0$, where the critical eigenvalue of mode $k$ is
positive, and is linearly stable in the reduced equation $\dot a = a\, G(a, d)$. Other Neumann modes
are not controlled, so nothing follows for the stability of the homogeneous state on $[0, L]$, nor
for the stability of the branch in the full reaction–diffusion system.

In the model $d_u, d_0 > 0$; the statement holds for all real values.
