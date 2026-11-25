# The reaction term inherits the Hölder remainder of the kinetics

Let $K$ be a compact topological space, $f : \mathbb{R}^2 \to \mathbb{R}^2$ continuous,
$a \in \mathbb{R}^2$, $J$ a real $2 \times 2$ matrix and $r$ real, $C \ge 0$ and $p \ge 0$, with sup
norms on $\mathbb{R}^2$ and on $C(K, \mathbb{R}^2)$. Suppose
$\lVert f(a + z) - f(a) - J z \rVert \le C \lVert z \rVert^p$ whenever $\lVert z \rVert \le r$. Then
the reaction term $F(w) = f \circ w$ satisfies, for every $y \in C(K, \mathbb{R}^2)$ with
$\lVert y \rVert \le r$,

$$\lVert F(a + y) - F(a) - J y \rVert \le C \lVert y \rVert^p,$$

where $a$ also denotes the constant field and $J y$ is the [pointwise action](pointwise-matrix.md)
$x \mapsto J\, y(x)$. The powers are real powers, with $0^0 = 1$. For $r > 0$ and $p > 1$ the
remainder is $o(\lVert y \rVert)$, so $F$ is Fréchet differentiable at the constant field $a$ with
derivative $y \mapsto J y$.
