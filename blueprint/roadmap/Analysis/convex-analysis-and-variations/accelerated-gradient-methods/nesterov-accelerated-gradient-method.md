# Nesterov's accelerated gradient method for smooth convex functions

Let $\beta > 0$ and let $f : \mathbb{R}^n \to \mathbb{R}$ be convex and $\beta$-smooth ($\nabla f$ is $\beta$-Lipschitz) with a minimizer $x^\star$. Let $\lambda_0 = 0$, $\lambda_t = (1 + \sqrt{1 + 4\lambda_{t-1}^2})/2$ and $\gamma_t = (1 - \lambda_t)/\lambda_{t+1}$, and from an arbitrary $x_1 = y_1$ iterate $y_{t+1} = x_t - \nabla f(x_t)/\beta$ and $x_{t+1} = (1 - \gamma_t)y_{t+1} + \gamma_ty_t$. Then for every $t \ge 1$, $f(y_t) - f(x^\star) \le 2\beta\|x_1 - x^\star\|^2/t^2$. Proof sketch: the recurrence gives $\lambda_{k+1}^2 - \lambda_{k+1} = \lambda_k^2$ and, by induction, $\lambda_k \ge (k+1)/2$ for $k \ge 1$. With $A_k = \lambda_k^2/\beta$, so that $A_0 = 0$ and $\beta(A_{k+1} - A_k)^2 = A_{k+1}$, and with the reindexed points $y^{\mathrm c}_k = y_{k+1}$, $x^{\mathrm c}_{k+1} = x_{k+1}$ and $z_k = \lambda_{k+1}x_{k+1} - (\lambda_{k+1} - 1)y_{k+1}$ (so $z_0 = x_1$), the iteration is the general accelerated scheme, whose Lyapunov function is nonincreasing; this gives $A_k(f(y_{k+1}) - f(x^\star)) \le \tfrac12\|x_1 - x^\star\|^2$, hence the bound for $t = k + 1 \ge 2$. For $t = 1$, the descent lemma at $x^\star$ gives $f(x_1) - f(x^\star) \le \tfrac\beta2\|x_1 - x^\star\|^2$. The projected stochastic subgradient bound $DG/\sqrt T$ for a closed convex feasible set with an adapted, conditionally unbiased oracle of bounded second moment is a separate statement; for a compact feasible set and an i.i.d. oracle with a uniform bound $\|G(x, z)\| \le M$ it is an instance of the robust stochastic approximation bound with the Euclidean distance-generating function $\tfrac12\|x\|^2$, after converting that bound's diameter constant; the closed convex feasible set with an adapted oracle of bounded second moment is not covered by that instance.

## Proof depends on

- [The Lyapunov function of the accelerated gradient method is bounded by its initial value](accelerated-lyapunov-le.md): the Lyapunov function of the general accelerated scheme is bounded by its initial value.
- [Descent lemma](../gradient-descent/gradient-descent-descent-lemma.md): the case $t = 1$.

## Background

- [Nesterov's $O(1/k^2)$ rate for accelerated gradient descent](nesterov-accelerated-rate.md): the same rate for a different polynomial step schedule.
- [Sublinear rate of gradient descent for smooth convex functions](../gradient-descent/gradient-descent-convex-sublinear-rate.md): the $O(1/t)$ rate without acceleration.
- [Expected error of robust stochastic approximation (mirror descent SA)](../mirror-descent/integral-robust-sa-average-sub-le.md): the stochastic projected method with an i.i.d. oracle.

## Sources

- S. Bubeck, "Convex optimization: algorithms and complexity", *Foundations and Trends in Machine Learning* 8(3–4):231–357, 2015, arXiv:1405.4980, §3.7.2, Theorem 3.19
