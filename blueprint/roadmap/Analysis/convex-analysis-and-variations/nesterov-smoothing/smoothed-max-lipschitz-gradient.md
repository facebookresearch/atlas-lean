# The smoothed max-type function has a Lipschitz gradient

Let $E, F$ be finite-dimensional real inner product spaces, $A : E \to F$ linear, $Q \subseteq F$ nonempty, compact and convex, $\varphi$ continuous and convex on $Q$, $d$ continuous and $\sigma$-strongly convex on $Q$ with $\sigma > 0$, and $\mu > 0$. Then the [smoothed max-type function](smoothed-max.md) $f_\mu$ is convex and differentiable, and

$$
\|\nabla f_\mu(x) - \nabla f_\mu(y)\| \le \frac{\|A\|^2}{\mu \sigma} \|x - y\| \qquad (x, y \in E).
$$

The source proves this for arbitrary norms on $E$ and $F$, with $\|A\|_{1,2}$ the operator norm between them and the dual norm on gradients; the statement here is the Euclidean special case, so it is weaker than the source. The source also identifies the gradient, $\nabla f_\mu(x) = A^* u_\mu(x)$ with $u_\mu(x)$ the unique maximiser, which is not part of this statement.

## Background

- [Uniform approximation by the smoothed function](smoothed-max-approximation.md): the approximation error $\mu D$ that balances this Lipschitz constant.
- [Optimal rate of Nesterov's scheme started at $\gamma_0 = L$](../accelerated-gradient-methods/estimate-sequence-optimal-rate.md): the optimal method applied to $f_\mu$ in the source's Theorem 3.

## Sources

- Yu. Nesterov, *Smooth minimization of non-smooth functions*, Math. Program. 103 (2005) 127–152, Theorem 1.
