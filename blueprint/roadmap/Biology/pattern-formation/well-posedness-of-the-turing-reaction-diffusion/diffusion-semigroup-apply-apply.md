# Each species evolves by the scalar operator at its own time

Let $K$ be a compact topological space, $H = (H(\tau))_{\tau \ge 0}$ any family of bounded linear
operators on $C(K, \mathbb{R})$, $d_u, d_v \ge 0$ and
$S(t) = \operatorname{diag}(H(d_u t), H(d_v t))$ the [diffusion operators](diffusion-semigroup.md).
Write $d_0 = d_u$ and $d_1 = d_v$. For every $t \ge 0$, every $w \in C(K, \mathbb{R}^2)$, every
$x \in K$ and every species index $k \in \{0, 1\}$,

$$\bigl(S(t)\, w\bigr)(x)_k = \bigl(H(d_k t)\, w_k\bigr)(x),$$

where $w_k \in C(K, \mathbb{R})$ is the [species-$k$ field](species-proj.md) $x \mapsto w(x)_k$.
Equivalently, as fields on $K$: the species-$k$ field of $S(t)\, w$ is $H(d_k t)$ applied to the
species-$k$ field of $w$, $(S(t)\, w)_k = H(d_k t)\, w_k$.
