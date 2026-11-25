# Local well-posedness of the Turing system for C¹ kinetics

Let $K$ be a compact topological space and let $C(K, \mathbb{R}^2)$ carry the sup norm, with the sup
norm $\max(|u|, |v|)$ on $\mathbb{R}^2$. Let $H$ be a C₀ semigroup on $C(K, \mathbb{R})$: a family
$(H(\tau))_{\tau \ge 0}$ of bounded linear operators with $H(0)$ the identity,
$H(\sigma + \tau) = H(\sigma) H(\tau)$, every orbit $\tau \mapsto H(\tau)\varphi$ continuous, and
$\lVert H(\tau) \rVert$ bounded on every bounded time interval. Let $d_u, d_v \ge 0$, let
$S(t) = \operatorname{diag}(H(d_u t), H(d_v t))$ be the
[diffusion semigroup](diffusion-semigroup.md) built from them, and let the reaction term be the
superposition operator $F(w) = f \circ w$ of kinetics $f : \mathbb{R}^2 \to \mathbb{R}^2$. Assume
$f$ is $C^1$.

A mild solution on $[0, T]$ from $w_0$ is a curve $w : \mathbb{R} \to C(K, \mathbb{R}^2)$ that is
continuous on $[0, T]$, such that for every $t \in [0, T]$ the integrand
$s \mapsto S(t - s) F(w(s))$ is integrable on $[0, t]$ and

$$w(t) = S(t)\,w_0 + \int_0^t S(t - s)\, F(w(s))\, ds.$$

Then for every radius $r$ there are a time $T > 0$, a bound $R$, a constant $C \ge 0$ and a solution
map $w_0 \mapsto w_{w_0}$, all chosen before the initial datum, such that:

- for every $w_0 \in C(K, \mathbb{R}^2)$ with $\lVert w_0 \rVert \le r$, the curve $w_{w_0}$ is
  continuous, is a mild solution on $[0, T]$ from $w_0$, and satisfies
  $\lVert w_{w_0}(t) \rVert \le R$ for $t \in [0, T]$;
- for $\lVert w_0 \rVert, \lVert y_0 \rVert \le r$ and $t \in [0, T]$,
  $\lVert w_{w_0}(t) - w_{y_0}(t) \rVert \le C \lVert w_0 - y_0 \rVert$.

Since $S(0)$ is the identity, $w_{w_0}(0) = w_0$. Mild solutions are
[unique](is-mild-solution-unique.md). With $K = \overline{\Omega}$ for a bounded domain $\Omega$ and
$H$ the Neumann heat semigroup, the mild solutions are those of the Turing system
$u_t = d_u \Delta u + f_1(u, v)$, $v_t = d_v \Delta v + f_2(u, v)$ with zero-flux boundary
conditions. In the model the diffusion coefficients are positive; the result also allows a species
that does not diffuse ($d_i = 0$).
