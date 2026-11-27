# Uniform last-iterate rate of a step schedule

A step schedule
$s : \mathbb{N} \to \mathbb{R}$ achieves a uniform last-iterate rate with exponent
$c \in \mathbb{R}$ if there are a real number $C > 0$ and an integer $K \ge 1$ with the following
property. For every $d \in \mathbb{N}$, every convex differentiable function
$f : \mathbb{R}^d \to \mathbb{R}$ whose gradient is $1$-Lipschitz for the Euclidean norm, every
$x^\star \in \mathbb{R}^d$ with $f(x^\star) \le f(x)$ for all $x$, every $x_0 \in \mathbb{R}^d$ and
every integer $k \ge K$, the $k$-th gradient descent iterate $x_k$ of $f$ from $x_0$ with steps
$s$ satisfies

$$f(x_k) - f(x^\star) \le \frac{C \lVert x_0 - x^\star \rVert^2}{k^c}.$$

The constants $C$ and $K$ are chosen before, and do not depend on, $d$, $f$, $x^\star$, $x_0$
and $k$.
