# Global convergence of the Dai–Yuan method

Let $E$ be a real Hilbert space and $f : E \to \mathbb{R}$, differentiable at the iterates, and write $g_k = \nabla f(x_k)$. Run
$x_{k+1} = x_k + \alpha_k d_k$ with $\alpha_k > 0$, $d_0 = -g_0$ and
$d_{k+1} = -g_{k+1} + \beta_k d_k$ with the [Dai–Yuan parameter](dai-yuan-beta.md)
$\beta_k = \|g_{k+1}\|^2 / d_k^\top (g_{k+1} - g_k)$, every step length satisfying the
[standard Wolfe conditions](../line-search-methods/wolfe-conditions.md) with constants $\delta > 0$
and $\sigma < 1$. Suppose $f(x_k)$ is bounded below,
$\|g_{k+1} - g_k\| \le L \|x_{k+1} - x_k\|$ for some $L > 0$, and no $g_k$ vanishes (otherwise
the method stops at a stationary point). Then

$$\liminf_{k \to \infty} \|g_k\| = 0 .$$

As for the [Zoutendijk condition](../line-search-methods/zoutendijk.md), the source assumes $f$
bounded below and $\nabla f$ Lipschitz near the level set (Assumption 3.1); these imply the
hypotheses used here. The point of the theorem is that, unlike the Fletcher–Reeves,
Polak–Ribière–Polyak and Hestenes–Stiefel methods, no strong Wolfe condition and no sufficient
descent condition is needed.

Proof (the source's): every $d_k$ is a descent direction. Squaring
$d_{k+1} + g_{k+1} = \beta_k d_k$ and dividing by $(g_{k+1}^\top d_{k+1})^2 = \beta_k^2 (g_k^\top d_k)^2$
gives

$$\frac{\|d_{k+1}\|^2}{(g_{k+1}^\top d_{k+1})^2} \le \frac{\|d_k\|^2}{(g_k^\top d_k)^2} + \frac{1}{\|g_{k+1}\|^2},$$

so $\|d_k\|^2 / (g_k^\top d_k)^2 \le \sum_{i \le k} \|g_i\|^{-2}$. If $\|g_k\| \ge c > 0$ for all $k$,
the terms of the Zoutendijk series are at least $c^2 / (k + 1)$, and the series diverges.

## Informally uses

- [Zoutendijk condition](../line-search-methods/zoutendijk.md): the summability that the recurrence
  contradicts (Lemma 3.2 of the source).
- [The Dai–Yuan identity](inner-dai-yuan-direction.md): equation (2.6), used to divide the squared
  recurrence.
- [Descent of the Dai–Yuan direction](inner-dai-yuan-direction-neg.md): the induction showing that
  every direction is a descent direction, (3.9)–(3.10).

## Sources

- Y. H. Dai and Y. Yuan, *A nonlinear conjugate gradient method with a strong global convergence property*, SIAM J. Optim. 10 (1999), 177–182, Theorem 3.3.
