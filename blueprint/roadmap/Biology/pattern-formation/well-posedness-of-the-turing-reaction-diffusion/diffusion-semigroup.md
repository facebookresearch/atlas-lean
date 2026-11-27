# Diagonal diffusion operators diag(H(d_u t), H(d_v t))

Let $K$ be a compact topological space, let $H = (H(\tau))_{\tau \ge 0}$ be any family of bounded
linear operators on $C(K, \mathbb{R})$ and let $d_u, d_v \ge 0$ be diffusion coefficients. For
$t \ge 0$, the diffusion operator $S(t)$ on $C(K, \mathbb{R}^2)$ applies $H(d_u t)$ to the first
species and $H(d_v t)$ to the second, $S(t) = \operatorname{diag}(H(d_u t), H(d_v t))$:

$$S(t)(u, v) = \bigl(H(d_u t)\, u,\; H(d_v t)\, v\bigr).$$

The definition does not require $H$ to be a semigroup. The intended case is the Neumann heat
semigroup $H(\tau) = e^{\tau \Delta_N}$ on $C(\overline{\Omega})$ for a bounded domain $\Omega$, for
which $S(t) = e^{t D \Delta_N}$ with $D = \operatorname{diag}(d_u, d_v)$ is the semigroup generated
by the linear part $D \Delta_N$ of the two-species reaction–diffusion system with zero-flux boundary
conditions. A coefficient $d_i = 0$ gives $H(0)$ on species $i$, the identity when $H$ is a
semigroup: that species does not diffuse.
