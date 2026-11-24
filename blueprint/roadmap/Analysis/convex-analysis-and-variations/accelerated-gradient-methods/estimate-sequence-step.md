# One step of Nesterov's estimate-sequence method contracts its potential

Let $E$ be a real Hilbert space, $f : E \to \mathbb{R}$ differentiable and $\mu$-strongly convex with $\mu \ge 0$, $L > 0$ and $u \in E$. Let $\alpha \in [0, 1]$, $\gamma \ge 0$ and $\gamma' > 0$ with $\gamma' = (1 - \alpha)\gamma + \alpha\mu = L\alpha^2$, and let $y, x', v'$ satisfy

$$
(\gamma + \alpha\mu)\, y = \alpha\gamma\, v + \gamma' x, \qquad
f(x') \le f(y) - \tfrac{1}{2L}\|\nabla f(y)\|^2, \qquad
\gamma' v' = (1 - \alpha)\gamma\, v + \alpha\mu\, y - \alpha \nabla f(y).
$$

Then

$$
f(x') - f(u) + \tfrac{\gamma'}{2}\|v' - u\|^2 \le (1 - \alpha)\Big(f(x) - f(u) + \tfrac{\gamma}{2}\|v - u\|^2\Big).
$$

This is one step of [Nesterov's general scheme](is-nesterov-scheme.md). The source proves $f(x_k) \le \varphi_k^*$ for the estimate functions $\varphi_k$ and then uses $\varphi_k(x) \le (1 - \lambda_k) f(x) + \lambda_k \varphi_0(x)$; evaluating that argument at a fixed point $u$ instead of minimising over $x$ gives this potential inequality, which holds for every $u$ and needs no minimiser of $f$. The proof combines the descent condition, convexity at $x$, $\mu$-strong convexity at $u$, the identity $(p + q)(p\|a\|^2 + q\|b\|^2) - \|pa + qb\|^2 = pq\|a - b\|^2$ with $p = (1 - \alpha)\gamma$, $q = \alpha\mu$, and the equation $L\alpha^2 = \gamma'$, which makes the $\|\nabla f(y)\|^2$ terms cancel; the choice of $y$ makes the remaining inner products cancel.

## Informally uses

- [First-order condition for strong convexity](../gradient-descent/add-inner-add-le-of-strong-convex-on.md): the lower models of $f$ at $y$, evaluated at $x$ and at $u$.

## Background

- [One step of the accelerated gradient method does not increase its Lyapunov function](accelerated-lyapunov-step.md): the analogous potential step for the three-sequence form of Wilson, Recht and Jordan, with weights $A_k$ in place of $\lambda_k^{-1}$.

## Sources

- Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course*, lecture notes, July 2, 1998 (draft of the 2004 Kluwer book *Introductory Lectures on Convex Optimization: A Basic Course*; the numbering cited here is that of the 1998 draft), Section 2.2.1: Lemmas 2.2.1–2.2.3 and the derivation of the General scheme (2.2.6), which together give the inductive step of the proof of Theorem 2.2.1.
