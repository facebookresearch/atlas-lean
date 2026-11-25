# Nesterov's $O(1/k^2)$ rate for accelerated gradient descent

Let $E$ be a real Hilbert space, $L > 0$, and $f : E \to \mathbb{R}$ convex and differentiable with $L$-Lipschitz gradient. Run the accelerated gradient method from $z_0 \in E$:

$$
x_{k+1} = \tfrac{k}{k+2}\, y_k + \tfrac{2}{k+2}\, z_k, \qquad
y_{k+1} = x_{k+1} - \tfrac{1}{L} \nabla f(x_{k+1}), \qquad
z_{k+1} = z_k - \tfrac{k+1}{2L} \nabla f(x_{k+1})
$$

(the point $y_0$ is never used, since $x_1 = z_0$). Then for every $u \in E$ and every $k \ge 1$,

$$
f(y_k) - f(u) \le \frac{2L\,\|z_0 - u\|^2}{k(k+1)}.
$$

With $u$ a minimizer this is the accelerated rate $O(L\|z_0 - x^\star\|^2/k^2)$, against $O(L\|x_0 - x^\star\|^2/k)$ for gradient descent with step $1/L$. No minimizer needs to exist for the inequality itself.

The method couples a gradient step ($y$) with a dual-averaging step of growing weight $a_k = (k+1)/(2L)$ ($z$); the proof applies [the bound on the Lyapunov function](accelerated-lyapunov-le.md) with $A_k = k(k+1)/(4L)$, for which $L(A_{k+1} - A_k)^2 \le A_{k+1}$ and the coupling weight is $\tau_k = (A_{k+1} - A_k)/A_{k+1} = 2/(k+2)$.

## Informally uses

- [The Lyapunov function of the accelerated gradient method is bounded by its initial value](accelerated-lyapunov-le.md): the bound $A_k(f(y_k) - f(u)) \le \|z_0 - u\|^2/2$, divided by $A_k$.

## Background

- [Sublinear rate of gradient descent for smooth convex functions](../gradient-descent/gradient-descent-convex-sublinear-rate.md): the unaccelerated $O(1/k)$ rate under the same hypotheses.
- [Su–Boyd–Candès rate](su-boyd-candes-rate.md): the continuous-time limit of this method and its $O(1/t^2)$ rate, with $t \approx k/\sqrt{L}$.
- [Lower complexity bound for smooth convex minimisation](../lower-complexity-bounds-for-first-order-methods/exists-lower-bound-smooth-convex.md): no method querying only gradients can improve the order $1/k^2$ while $k \le (n-1)/2$.

## Sources

- Y. Nesterov, *A method of solving a convex programming problem with convergence rate $O(1/k^2)$*, Soviet Math. Dokl. 27 (1983) 372–376 (the accelerated $O(1/k^2)$ rate; the three-sequence form of the method used here is the family (19) of Wilson, Recht and Jordan).
- A. C. Wilson, B. Recht and M. I. Jordan, *A Lyapunov analysis of momentum methods in optimization*, arXiv:1611.02635v4 (the version containing this material), Section 3.1: the accelerated family (19a)–(19c), the discrete Lyapunov function (21), and Proposition 5 with Lemma 6, whose error bound (26a) for the gradient map $G_\epsilon$ of (25) is $\le 0$ exactly when $(A_{k+1} - A_k)^2 \le A_{k+1}/L$. The parameters $A_k$, $\tau_k$ and the constant $2L$ are this formalization's choice.
