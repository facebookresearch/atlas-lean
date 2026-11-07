# Cauchy–Kovalevskaya theorem

Let $d$ be a natural number, write $\mathbb{R}^d$ for real
Euclidean $d$-space, and let $F : \mathbb{R}^d \times \mathbb{R} \times \mathbb{R} \to
\mathbb{R}^d$, $f : \mathbb{R}^d \times \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ and
$u_0 : \mathbb{R}^d \to \mathbb{R}$ be real analytic at every point. Then for every
$x_0 \in \mathbb{R}^d$ there are an open set $U \subseteq \mathbb{R}^d \times \mathbb{R}$
containing $(x_0, 0)$ and a function $u : \mathbb{R}^d \times \mathbb{R} \to \mathbb{R}$, real
analytic on $U$, such that $u(x, 0) = u_0(x)$ whenever $(x, 0) \in U$ and

$$\partial_t u(x, t) = F(x, t, u(x, t)) \cdot \nabla_x u(x, t) + f(x, t, u(x, t))$$

for every $(x, t) \in U$, where $\partial_t u$ is the partial derivative of $u$ in $t$ and
$\nabla_x u$ is its gradient in $x$. Moreover, every function
$v : \mathbb{R}^d \times \mathbb{R} \to \mathbb{R}$ that is real analytic on $U$, satisfies
$v(x, 0) = u_0(x)$ whenever $(x, 0) \in U$, and satisfies the same equation at every point of
$U$ agrees with $u$ on $U$.

## Sources

- A.-L. Cauchy (1842) and S. Kovalevskaya (1875). Listed as §32 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `cauchy_kovalevskaya`.
