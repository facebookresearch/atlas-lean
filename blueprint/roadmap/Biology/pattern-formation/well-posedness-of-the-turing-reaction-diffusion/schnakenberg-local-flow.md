# Local well-posedness of the Schnakenberg–Turing system

Let $K$ be a compact topological space and let $C(K, \mathbb{R}^2)$ carry the sup norm, with the sup
norm $\max(|u|, |v|)$ on $\mathbb{R}^2$. Let $H$ be a C₀ semigroup on $C(K, \mathbb{R})$: a family
$(H(\tau))_{\tau \ge 0}$ of bounded linear operators with $H(0)$ the identity,
$H(\sigma + \tau) = H(\sigma) H(\tau)$, every orbit $\tau \mapsto H(\tau)\varphi$ continuous, and
$\lVert H(\tau) \rVert$ bounded on every bounded time interval. Let $d_u, d_v \ge 0$, let
$S(t) = \operatorname{diag}(H(d_u t), H(d_v t))$ be the
[diffusion semigroup](diffusion-semigroup.md), let $a, b$ be real, and let the reaction term be
$F(w) = f \circ w$ for the
[Schnakenberg kinetics](../turing-patterns-and-diffusion-driven-instability/schnakenberg.md)
$f(u, v) = (a - u + u^2 v,\ b - u^2 v)$. A mild solution on $[0, T]$ from $w_0$ is a curve
$w : \mathbb{R} \to C(K, \mathbb{R}^2)$ that is continuous on $[0, T]$, such that for every
$t \in [0, T]$ the integrand $s \mapsto S(t - s) F(w(s))$ is integrable on $[0, t]$ and

$$w(t) = S(t)\,w_0 + \int_0^t S(t - s)\, F(w(s))\, ds.$$

Then for every radius $r$ there are a time $T > 0$, a bound $R$, a constant $C \ge 0$ and a solution
map $w_0 \mapsto w_{w_0}$, all chosen before the initial datum, such that:

- for every $w_0 \in C(K, \mathbb{R}^2)$ with $\lVert w_0 \rVert \le r$, the curve $w_{w_0}$ is
  continuous, is a mild solution on $[0, T]$ from $w_0$, and satisfies
  $\lVert w_{w_0}(t) \rVert \le R$ for $t \in [0, T]$;
- for $\lVert w_0 \rVert, \lVert y_0 \rVert \le r$ and $t \in [0, T]$,
  $\lVert w_{w_0}(t) - w_{y_0}(t) \rVert \le C \lVert w_0 - y_0 \rVert$.

Mild solutions are [unique](is-mild-solution-unique.md). Biologically $a, b > 0$ and $d_u, d_v > 0$;
the result holds for all real $a, b$ and all $d_u, d_v \ge 0$.
