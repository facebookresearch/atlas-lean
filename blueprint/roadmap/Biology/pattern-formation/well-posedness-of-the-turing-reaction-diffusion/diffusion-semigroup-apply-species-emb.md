# Single-species eigenfunctions of the diffusion operators

Let $K$ be a compact topological space, $H = (H(\tau))_{\tau \ge 0}$ any family of bounded linear
operators on $C(K, \mathbb{R})$, $d_u, d_v \ge 0$ (with $d_0 = d_u$, $d_1 = d_v$) and
$S(t) = \operatorname{diag}(H(d_u t), H(d_v t))$ the [diffusion operators](diffusion-semigroup.md).
Suppose $\varphi \in C(K, \mathbb{R})$ and $q \in \mathbb{R}$ satisfy
$H(\tau)\varphi = e^{-q\tau}\varphi$ for every $\tau \ge 0$. Then for every $t \ge 0$ and every
species index $i \in \{0, 1\}$, the [single-species field](species-emb.md) $\varphi\, e_i$ satisfies

$$S(t)(\varphi\, e_i) = e^{-q d_i t}\, \varphi\, e_i.$$

For the Neumann heat semigroup on $[0, L]$ with $L > 0$, the functions $\varphi(x) = \cos(k_n x)$
with the
[Neumann wavenumbers](../turing-patterns-and-diffusion-driven-instability/neumann-wavenumber.md)
$k_n = n\pi/L$ satisfy the hypothesis with $q = k_n^2$.
