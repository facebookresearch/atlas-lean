# Zoutendijk condition

Let $E$ be a real Hilbert space (for instance $\mathbb{R}^n$) and $f : E \to \mathbb{R}$, differentiable at
the iterates. Consider a line-search method $x_{k+1} = x_k + \alpha_k d_k$ with $\alpha_k > 0$ and descent
directions, $g_k^\top d_k < 0$ where $g_k = \nabla f(x_k)$, whose step lengths satisfy the
[standard Wolfe conditions](wolfe-conditions.md) with constants $\delta > 0$ and $\sigma < 1$.
Suppose that $f(x_k)$ is bounded below and that
$\|g_{k+1} - g_k\| \le L\, \|x_{k+1} - x_k\|$ for some $L > 0$. Then

$$\sum_{k \ge 0} \frac{(g_k^\top d_k)^2}{\|d_k\|^2} < \infty .$$

Since $(g_k^\top d_k)^2 / \|d_k\|^2 = \cos^2\theta_k\, \|g_k\|^2$, where $\theta_k$ is the angle
between $d_k$ and $-g_k$, this is the classical form $\sum_k \cos^2\theta_k \|g_k\|^2 < \infty$: if
the angles stay away from $90^\circ$ (steepest descent, or quasi-Newton directions with bounded
condition numbers), then $g_k \to 0$.

The source assumes $f$ bounded below on $\mathbb{R}^n$ and $\nabla f$ Lipschitz on a
neighbourhood of the level set $\{x : f(x) \le f(x_0)\}$ (its Assumption 3.1). The Armijo condition
keeps the iterates in the level set, so these assumptions imply the two used here, which are the
ones the proof uses.

Proof (the source's): the curvature condition and the Lipschitz bound give
$(\sigma - 1) g_k^\top d_k \le (g_{k+1} - g_k)^\top d_k \le \alpha_k L \|d_k\|^2$, a lower bound on
$\alpha_k$; the Armijo condition turns it into
$f(x_k) - f(x_{k+1}) \ge \delta(1 - \sigma) L^{-1} (g_k^\top d_k)^2 / \|d_k\|^2$, and the sum
telescopes.

## Informally uses

- [Armijo sufficient decrease condition](armijo-condition.md): turns the step lower bound into
  objective decrease, equation (3.6) of the source.
- [Wolfe curvature condition](curvature-condition.md): with the Lipschitz bound, gives the step
  lower bound (3.3)–(3.5).

## Sources

- Y. H. Dai and Y. Yuan, *A nonlinear conjugate gradient method with a strong global convergence property*, SIAM J. Optim. 10 (1999), 177–182, Lemma 3.2 (essentially due to Zoutendijk and Wolfe).
- Y. H. Dai and Y. Yuan, *A note on the nonlinear conjugate gradient method*, J. Comput. Math. 20 (2002); https://lsec.cc.ac.cn/pub/yyx/papers/jcm1290.pdf, Lemma 2.2.
