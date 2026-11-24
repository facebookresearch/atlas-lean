# Linear rate of the accelerated gradient method for strongly convex functions

Let $E$ be a real Hilbert space, $f : E \to \mathbb{R}$ differentiable and $\mu$-strongly convex with $L$-Lipschitz gradient, $0 < \mu \le L$, and $q = \sqrt{\mu / L}$. Run, from $v_0 = x_0$,

$$
y_k = \frac{x_k + q\, v_k}{1 + q}, \qquad
x_{k+1} = y_k - \tfrac{1}{L} \nabla f(y_k), \qquad
v_{k+1} = (1 - q)\, v_k + q\, y_k - \tfrac{q}{\mu} \nabla f(y_k).
$$

Then for every $u \in E$ and every $k$,

$$
f(x_k) - f(u) \le \Big(1 - \sqrt{\mu / L}\Big)^k \Big(f(x_0) - f(u) + \tfrac{\mu}{2}\|x_0 - u\|^2\Big).
$$

This is [Nesterov's general scheme](is-nesterov-scheme.md) with the gradient step (Constant Step Scheme I of the source) and $\gamma_0 = \mu$, for which $\gamma_k = \mu$ and $\alpha_k = \sqrt{\mu/L}$ for every $k$. The source obtains the bound for $u = x^*$ from Theorem 2.2.1 and the first bound of Lemma 2.2.4; here it holds for every $u$. Eliminating $v_k$ gives the familiar momentum form $y_{k+1} = x_{k+1} + \frac{1 - q}{1 + q}(x_{k+1} - x_k)$ (scheme (2.2.8) of the source).

The number of iterations to reach accuracy $\varepsilon$ is $O(\sqrt{L/\mu}\,\log(1/\varepsilon))$, against $O((L/\mu)\log(1/\varepsilon))$ for gradient descent, and the [lower complexity bound for strongly convex functions](../lower-complexity-bounds-for-first-order-methods/exists-lower-bound-strongly-convex.md) shows that the factor $\sqrt{L/\mu}$ cannot be improved by more than a constant.

## Informally uses

- [Convergence of Nesterov's estimate-sequence scheme](estimate-sequence-rate.md): applied with $\alpha_k = \sqrt{\mu/L}$ and $\gamma_k = \mu$, for which $\lambda_k = (1 - \sqrt{\mu/L})^k$.
- [Nesterov's general optimal scheme](is-nesterov-scheme.md): the three recursions above are an instance.
- [Sufficient decrease of a gradient step](../gradient-descent/gradient-descent-sufficient-decrease.md): the gradient step satisfies the descent condition.

## Background

- [Linear convergence of gradient descent for strongly convex functions](../gradient-descent/gradient-descent-strongly-convex-linear.md): the unaccelerated linear rate $1 - \eta\mu$.
- [Lower complexity bound for smooth strongly convex minimisation](../lower-complexity-bounds-for-first-order-methods/exists-lower-bound-strongly-convex.md): the matching lower bound.

## Sources

- Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course*, lecture notes, July 2, 1998 (draft of the 2004 Kluwer book *Introductory Lectures on Convex Optimization: A Basic Course*; the numbering cited here is that of the 1998 draft), Section 2.2.1: Constant Step Scheme I (2.2.7), Theorem 2.2.1 and Lemma 2.2.4.
