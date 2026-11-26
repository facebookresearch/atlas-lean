# The Lyapunov function of the accelerated gradient method is bounded by its initial value

Let $E$ be a real Hilbert space, $L > 0$, $f : E \to \mathbb{R}$ convex and differentiable with $L$-Lipschitz gradient, and $u \in E$. Let $(A_k)$ be nondecreasing with $A_0 \ge 0$ and $L(A_{k+1} - A_k)^2 \le A_{k+1}$, and let $(x_k), (y_k), (z_k)$ satisfy, for every $k$,

$$
A_{k+1} x_{k+1} = A_k y_k + (A_{k+1} - A_k) z_k, \quad
y_{k+1} = x_{k+1} - \tfrac1L \nabla f(x_{k+1}), \quad
z_{k+1} = z_k - (A_{k+1} - A_k)\nabla f(x_{k+1}).
$$

Then for every $k$, with $\mathcal E_k = A_k(f(y_k) - f(u)) + \tfrac12\|z_k - u\|^2$,

$$
\mathcal E_k \le \mathcal E_0 .
$$

The growth condition $L(A_{k+1} - A_k)^2 \le A_{k+1}$ caps $A_k$ at order $k^2/L$, which is where the $O(1/k^2)$ rate comes from.

## Informally uses

- [One step of the accelerated gradient method does not increase its Lyapunov function](accelerated-lyapunov-step.md): applied at every step, then induction on $k$.

## Sources

- A. C. Wilson, B. Recht and M. I. Jordan, *A Lyapunov analysis of momentum methods in optimization*, arXiv:1611.02635v4 (the version containing this material), Section 3.1: the accelerated family (19a)–(19c), the discrete Lyapunov function (21), and Proposition 5 with Lemma 6, whose error bound (26a) for the gradient map $G_\epsilon$ of (25) is $\le 0$ exactly when $(A_{k+1} - A_k)^2 \le A_{k+1}/L$.
