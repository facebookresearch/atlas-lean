# Reduced pattern branch and sign change of the critical eigenvalue

Let $J = \begin{pmatrix} f_u & f_v \\ g_u & g_v \end{pmatrix}$ be a real $2 \times 2$ matrix (the
Jacobian of the kinetics at a homogeneous steady state), let $d_u$ and $k$ be real with
$f_u k^2 - d_u k^4 > 0$ (an admissible mode), let $d_0 = d_n(k^2)$ be its
[neutral diffusion](neutral-diffusion.md), assume $\operatorname{tr} J - k^2 (d_u + d_0) < 0$, and
write $D(d) = \operatorname{diag}(d_u, d)$. Let $G : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ be
strictly differentiable at $(0, d_0)$ with derivative $G'$, and equal on the trivial branch to the
critical eigenvalue: $G(0, d) = \lambda_+(J - k^2 D(d))$ for all $d$ near $d_0$, with $\lambda_+$
the [leading real eigenvalue](leading-eigenvalue.md). Then:

- the crossing is transversal: $\partial_d G(0, d_0) = G'(0, 1) > 0$;
- there is $\varphi : \mathbb{R} \to \mathbb{R}$ with $\varphi(0) = d_0$, strictly differentiable at
  $0$ with derivative $-G'(1, 0)/G'(0, 1)$, such that near $(0, d_0)$, $a\, G(a, d) = 0$ if and only
  if $a = 0$ or $d = \varphi(a)$;
- $G(0, d) < 0$ for $d < d_0$ and $G(0, d) > 0$ for $d > d_0$, for $d$ near $d_0$.

In applications $G$ comes from a center-manifold reduction, or from a Lyapunov–Schmidt reduction
along the $d$-dependent critical eigenvector; a reduction along a fixed kernel vector matches the
critical eigenvalue only to first order at $d_0$, which is the setting of the
[Turing pattern branch from the Lyapunov–Schmidt reduction](turing-pattern-branch-of-reduction.md).
Only the mode $k$ is controlled: another Neumann mode may already be unstable at $d_0$, so this is
not an exchange of stability of the homogeneous state on $[0, L]$.

In the model $d_u, d_0 > 0$; the statement holds for all real values.
