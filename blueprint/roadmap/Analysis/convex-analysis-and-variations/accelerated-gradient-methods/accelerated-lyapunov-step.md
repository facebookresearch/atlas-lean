# One step of the accelerated gradient method does not increase its Lyapunov function

Let $E$ be a real Hilbert space, $L > 0$, $f : E \to \mathbb{R}$ convex and differentiable with $L$-Lipschitz gradient, and $u \in E$. Let $0 \le A \le A'$ with $L(A' - A)^2 \le A'$, and from $y, z \in E$ take

$$
A' x' = A\, y + (A' - A)\, z, \qquad y' = x' - \tfrac{1}{L}\nabla f(x'), \qquad z' = z - (A' - A)\nabla f(x').
$$

Then

$$
A'\,(f(y') - f(u)) + \tfrac12\|z' - u\|^2 \le A\,(f(y) - f(u)) + \tfrac12\|z - u\|^2 .
$$

Proof: with $g = \nabla f(x')$ and $a = A' - A$, expand $\tfrac12\|z' - u\|^2 = \tfrac12\|z - u\|^2 - a\langle g, z - u\rangle + \tfrac{a^2}{2}\|g\|^2$; bound $f(y') \le f(x') - \|g\|^2/(2L)$ by sufficient decrease; bound $A(f(x') - f(y)) + a(f(x') - f(u))$ by $A\langle g, x' - y\rangle + a\langle g, x' - u\rangle = a\langle g, z - u\rangle$ using convexity and the coupling. What remains is $(a^2 - A'/L)\|g\|^2/2 \le 0$.

## Informally uses

- [Sufficient decrease of a gradient step](../gradient-descent/gradient-descent-sufficient-decrease.md): $f(y') \le f(x') - \|\nabla f(x')\|^2/(2L)$ for the step $1/L$.
- [First-order condition for convexity](../first-order-conditions-for-convexity/add-fderiv-le-of-convex-on.md): $f(x') + \langle \nabla f(x'), w - x'\rangle \le f(w)$ at $w = y$ and $w = u$.

## Background

- [Bregman divergence](../mirror-descent/bregman.md): the $z$-update is a mirror-descent step for $h = \|\cdot\|^2/2$, and (21) of Wilson, Recht and Jordan uses $D_h(u, z_k)$ in general.

## Sources

- A. C. Wilson, B. Recht and M. I. Jordan, *A Lyapunov analysis of momentum methods in optimization*, arXiv:1611.02635v4 (the version containing this material), Section 3.1: the accelerated family (19a)–(19c), the discrete Lyapunov function (21), and Proposition 5 with Lemma 6, whose error bound (26a) for the gradient map $G_\epsilon$ of (25) is $\le 0$ exactly when $(A_{k+1} - A_k)^2 \le A_{k+1}/L$. Here $h = \|\cdot\|^2/2$ and the map $\mathcal G$ of (19c) is a gradient step with step $1/L$.
