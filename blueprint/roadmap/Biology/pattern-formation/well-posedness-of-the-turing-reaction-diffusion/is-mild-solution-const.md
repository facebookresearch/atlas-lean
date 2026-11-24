# If H fixes constants, homogeneous steady states are mild solutions

Let $K$ be a compact topological space, $H = (H(\tau))_{\tau \ge 0}$ any family of bounded linear
operators on $C(K, \mathbb{R})$ with $H(\tau)\, 1 = 1$ for every $\tau \ge 0$, $d_u, d_v \ge 0$, and
$S(t) = \operatorname{diag}(H(d_u t), H(d_v t))$ the [diffusion operators](diffusion-semigroup.md).
Let the kinetics $f : \mathbb{R}^2 \to \mathbb{R}^2$ be continuous, with reaction term
$F(w) = f \circ w$, and let $c \in \mathbb{R}^2$ be a zero of $f$. A mild solution on $[0, T]$ from
$w_0$ is a curve $w : \mathbb{R} \to C(K, \mathbb{R}^2)$ that is continuous on $[0, T]$, such that
for every $t \in [0, T]$ the integrand $s \mapsto S(t - s) F(w(s))$ is integrable on $[0, t]$ and

$$w(t) = S(t)\,w_0 + \int_0^t S(t - s)\, F(w(s))\, ds.$$

Then for every real $T$ the constant curve equal to the constant field $c$ is a mild solution on
$[0, T]$ from $c$. This homogeneous steady state is the base state of the Turing instability
analysis. The hypothesis on $H$ holds for the Neumann heat semigroup but not for the Dirichlet one.
