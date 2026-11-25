# Variation of constants on a compact interval

Let $X$ be a real Banach space and $U$ a real normed space, let $A : X \to X$ and $B : U \to X$ be bounded linear operators, let $a \le b$, let $u : [a, b] \to U$ be continuous, and let $x_0 \in X$. Define $x : [a, b] \to X$ by

$$x(t) = e^{(t - a)A} x_0 + \int_a^t e^{(t - s)A} B u(s)\, ds .$$

1. **Existence.** $x(a) = x_0$, and $x$ is differentiable on $[a, b]$, with one-sided derivatives at the endpoints, and $x'(t) = A x(t) + B u(t)$ for every $t \in [a, b]$.
2. **Uniqueness on the interval.** If $y : [a, b] \to X$ is differentiable on $[a, b]$ in the same sense, $y(a) = x_0$ and $y'(t) = A y(t) + B u(t)$ for every $t \in [a, b]$, then $y = x$ on $[a, b]$.
3. **Clamped extension.** Let $\bar u(t) = u(\min(\max(t, a), b))$ for $t \in \mathbb{R}$. Then $\bar u$ is continuous on $\mathbb{R}$ and equal to $u$ on $[a, b]$, and the whole-line solution of $z' = Az + B\bar u$, $z(a) = x_0$, given by Duhamel's formula, restricts to $x$ on $[a, b]$.

When $a = b$ the interval is the single point $a$, $x(a) = x_0$, and the statements hold with derivatives on $[a, a]$ read as vacuous conditions. Uniqueness is claimed only on $[a, b]$: two continuous extensions of $u$ to $\mathbb{R}$ give whole-line solutions that agree on $[a, b]$ but in general differ outside it. For matrices, $X = \mathbb{R}^n$, $U = \mathbb{R}^m$ and $A$, $B$ act by matrix multiplication; a single-input single-output system is the case $m = 1$ with a scalar output read off by a fixed linear map.

**Proof.** The function $\bar u$ is a composition of continuous maps, so it is continuous, and it equals $u$ on $[a, b]$. By Duhamel's formula, $z(t) = e^{(t - a)A} x_0 + \int_a^t e^{(t - s)A} B\bar u(s)\, ds$ satisfies $z(a) = x_0$ and $z'(t) = A z(t) + B\bar u(t)$ for every real $t$. For $t \in [a, b]$ the integral only involves $s \in [a, t] \subseteq [a, b]$, where $\bar u = u$, so $z = x$ on $[a, b]$; this is part 3, and part 1 follows by restricting the two-sided derivative of $z$ to $[a, b]$. For part 2, let $w = y - x$. Then $w(a) = 0$ and $w' = A w$ on $[a, b]$, so $v(t) = e^{-(t - a)A} w(t)$ is differentiable on $[a, b]$ with $v'(t) = -A e^{-(t - a)A} w(t) + e^{-(t - a)A} A w(t) = 0$, because $A$ commutes with its exponential. A function on an interval with zero derivative everywhere is constant, so $v(t) = v(a) = 0$, and $w(t) = e^{(t - a)A} v(t) = 0$.

## Proof depends on

- [Duhamel's formula (variation of constants)](duhamel-variation-of-constants.md): the whole-line solution and its uniqueness for continuous forcing

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Appendix C, the variation of parameters formula (C.26), p. 488, for $\xi' = A(t)\xi + \nu$ on $\mathbb{K}^n$ with locally integrable $\nu$ on an interval $[\sigma_0, t]$. The Banach-space form with continuous forcing, the clamped extension and the interval uniqueness argument are derived on the page.
