# Local stable and unstable sets at a hyperbolic fixed point

Let $f : \mathbb{R}^n \to
\mathbb{R}^n$ be continuously differentiable on a neighbourhood of a point $x_0$ with
$f(x_0) = x_0$, and suppose that the derivative $Df(x_0)$ is invertible and hyperbolic. Then
there is an open set $U$ containing $x_0$ such that the local stable set
$W^s = \{x : f^k(x) \in U \text{ for all } k \ge 0 \text{ and } f^k(x) \to x_0 \text{ as }
k \to \infty\}$ and the local unstable set $W^u$, consisting of the points $x$ for which there
is a sequence $(y_k)_{k \ge 0}$ in $U$ with $y_0 = x$, $f(y_{k+1}) = y_k$ for all $k$ and
$y_k \to x_0$, satisfy $W^s \cap W^u = \{x_0\}$.

This is only the set-level part of the Hadamard–Perron theorem: it does not assert that $W^s$
and $W^u$ are $C^1$ submanifolds tangent to the stable and unstable subspaces of $Df(x_0)$.

## Sources

- J. Hadamard, 'Sur l'itération et les solutions asymptotiques des équations différentielles', Bull. Soc. Math. France 29 (1901); O. Perron, 'Über Stabilität und asymptotisches Verhalten der Integrale von Differentialgleichungssystemen', Math. Z. 29 (1929) 129–160. Listed as §104 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `stable_unstable_manifolds`.
