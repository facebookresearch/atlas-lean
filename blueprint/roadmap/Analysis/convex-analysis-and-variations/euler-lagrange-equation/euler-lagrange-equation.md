# Euler–Lagrange equation

Let $a < b$ be real numbers, let $L(t, y, v)$ be a real function
of three real variables that is twice continuously differentiable on $\mathbb{R}^3$, and let
$x : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable. Write
$\partial L / \partial y$ and $\partial L / \partial v$ for the partial derivatives of $L$ in its
second and third arguments. If $x$ is a variational extremum of the action of $L$ on $(a, b)$,
then for every $t \in (a, b)$

$$
\frac{\partial L}{\partial y}(t, x(t), x'(t))
= \frac{d}{ds}\Big|_{s = t} \frac{\partial L}{\partial v}(s, x(s), x'(s)).
$$

## Sources

- L. Euler (1744) and J.-L. Lagrange (1755). Listed as §44 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Problem `euler_lagrange_equation` of the lean-eval benchmark.
