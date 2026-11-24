# Mild solutions of the Turing system with C¹ kinetics are unique

Let $K$ be a compact topological space and let $C(K, \mathbb{R}^2)$ carry the sup norm, with the sup
norm $\max(|u|, |v|)$ on $\mathbb{R}^2$. Let $H$ be a C₀ semigroup on $C(K, \mathbb{R})$: a family
$(H(\tau))_{\tau \ge 0}$ of bounded linear operators with $H(0)$ the identity,
$H(\sigma + \tau) = H(\sigma) H(\tau)$, every orbit $\tau \mapsto H(\tau)\varphi$ continuous, and
$\lVert H(\tau) \rVert$ bounded on every bounded time interval. Let $d_u, d_v \ge 0$, let
$S(t) = \operatorname{diag}(H(d_u t), H(d_v t))$ be the
[diffusion semigroup](diffusion-semigroup.md) built from them, and let the reaction term be the
superposition operator $F(w) = f \circ w$ of kinetics $f : \mathbb{R}^2 \to \mathbb{R}^2$. Assume
$f$ is $C^1$. A mild solution on $[0, T]$ from $w_0$ is a curve
$w : \mathbb{R} \to C(K, \mathbb{R}^2)$ that is continuous on $[0, T]$, such that for every
$t \in [0, T]$ the integrand $s \mapsto S(t - s) F(w(s))$ is integrable on $[0, t]$ and

$$w(t) = S(t)\,w_0 + \int_0^t S(t - s)\, F(w(s))\, ds.$$

For every real $T$ and every $w_0 \in C(K, \mathbb{R}^2)$, two mild solutions on $[0, T]$ from the
same $w_0$ agree at every $t \in [0, T]$.
