# $C^2$ Taylor bound $H\delta^2/2$ when $-H\le f''\le H$ on an interval

Let $f : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable on $\mathbb{R}$, let
$a$, $b$ and $H$ be real numbers with $|f''(y)| \le H$, that is $-H \le f''(y) \le H$, for every
$y \in [a, b]$, and let $x$ and $x + \delta$ both lie in the interval $[a, b]$. Then the error
of the first-order Taylor approximation satisfies

$$\bigl|f(x + \delta) - f(x) - f'(x)\,\delta\bigr| \le \frac{H}{2}\,\delta^2 .$$

The bound on $f''$ is needed only on $[a, b]$, while the smoothness is assumed on all of
$\mathbb{R}$; since $x \in [a, b]$, the hypothesis forces $H \ge 0$. For $\delta \ne 0$, Taylor's
theorem with the Lagrange remainder writes the error as $f''(\xi)\,\delta^2 / 2$ for some $\xi$
strictly between $x$ and $x + \delta$, a point of $[a, b]$.
