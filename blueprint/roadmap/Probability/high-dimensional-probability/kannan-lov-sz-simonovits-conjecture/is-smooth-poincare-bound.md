# Smooth Poincaré bounds

Let $\mu$ be a measure on $\mathbb{R}^n$ and let
$C \in [0, \infty]$. For a differentiable $g : \mathbb{R}^n \to \mathbb{R}$ write
$\|\nabla g(x)\|$ for the Euclidean norm of the gradient of $g$ at $x$ (equivalently, the
operator norm of the derivative of $g$ at $x$). Then $C$ is a smooth Poincaré bound for $\mu$
if for every infinitely differentiable function $f : \mathbb{R}^n \to \mathbb{R}$ such that
$f$, $f^2$ and $\|\nabla f\|^2$ are $\mu$-integrable,

$$\int \Big(f(x) - \int f \, d\mu\Big)^2 \, d\mu(x) \le C \int \|\nabla f(x)\|^2 \, d\mu(x),$$

where the outer integral on the left and the integral on the right are computed in
$[0, \infty]$ with $0 \cdot \infty = 0$, and the inner integral $\int f \, d\mu$ is the usual
real integral. The measure $\mu$ need not be a probability measure.
