# The diffusion operators of a C₀ semigroup form a C₀ semigroup

Let $K$ be a compact topological space, with the sup norm on $C(K, \mathbb{R})$ and on
$C(K, \mathbb{R}^2)$ (and $\max(|u|, |v|)$ on $\mathbb{R}^2$). Call a family $(T(t))_{t \ge 0}$ of
bounded linear operators on a normed space a C₀ semigroup when $T(0)$ is the identity,
$T(s + t) = T(s)\, T(t)$, every orbit $t \mapsto T(t) x$ is continuous on $[0, \infty)$ and
$\lVert T(t) \rVert$ is bounded on every interval $[0, T_0]$.

If $H$ is a C₀ semigroup on $C(K, \mathbb{R})$, then for all diffusion coefficients $d_u, d_v \ge 0$
the [diffusion operators](diffusion-semigroup.md) $S(t) = \operatorname{diag}(H(d_u t), H(d_v t))$
form a C₀ semigroup on $C(K, \mathbb{R}^2)$. The intended $H$ is the Neumann heat semigroup on
$C(\overline{\Omega})$, which this result takes as given.
