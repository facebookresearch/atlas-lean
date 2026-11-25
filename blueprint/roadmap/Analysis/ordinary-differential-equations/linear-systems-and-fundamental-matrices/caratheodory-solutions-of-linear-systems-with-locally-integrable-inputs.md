# Carathéodory solutions of linear systems with locally integrable inputs

Let $A \in \mathbb{R}^{n \times n}$ and $B \in \mathbb{R}^{n \times m}$, let $a < b$, let $u : [a, b] \to \mathbb{R}^m$ be Lebesgue integrable, and let $x_0 \in \mathbb{R}^n$. Call $x : [a, b] \to \mathbb{R}^n$ a **Carathéodory solution** of $\dot x = Ax + Bu$, $x(a) = x_0$, if $x$ is absolutely continuous, $x(a) = x_0$, and $\dot x(t) = A x(t) + B u(t)$ for almost every $t \in [a, b]$; equivalently, $x(t) = x_0 + \int_a^t (A x(s) + B u(s))\, ds$ for every $t$.

1. **Existence.** $x(t) = e^{(t - a)A} x_0 + \int_a^t e^{(t - s)A} B u(s)\, ds$ is a Carathéodory solution.
2. **Uniqueness.** It is the only one.
3. **Continuous dependence.** If $x$ and $\tilde x$ are the solutions for inputs $u$ and $\tilde u$ and initial states $x_0$ and $\tilde x_0$, then $\sup_{[a, b]}\|x - \tilde x\| \le e^{(b - a)\|A\|}\big(\|x_0 - \tilde x_0\| + \|B\|\int_a^b \|u - \tilde u\|\big)$.

Piecewise-continuous and bounded measurable inputs are special cases. The solution is in general differentiable only almost everywhere: for a step input, $\dot x$ jumps at the step.

**Proof.** For part 1, write $x(t) = e^{(t - a)A}\big(x_0 + \int_a^t e^{-(s - a)A} B u(s)\, ds\big)$. The bracket is an indefinite integral of an integrable function, hence absolutely continuous with derivative $e^{-(t - a)A} B u(t)$ almost everywhere (Lebesgue differentiation), and the product with the smooth matrix function $e^{(t - a)A}$ is absolutely continuous with $\dot x = A x + B u$ almost everywhere. For parts 2 and 3, the difference $w = x - \tilde x$ of two Carathéodory solutions satisfies $w(t) = w(a) + \int_a^t (A w + B(u - \tilde u))\, ds$, so $\|w(t)\| \le \|w(a)\| + \|B\|\int_a^b \|u - \tilde u\| + \|A\|\int_a^t \|w\|$, and Grönwall's inequality gives part 3; with the same data, part 3 gives $w = 0$, which is part 2.

## Background

- [Duhamel's formula (variation of constants)](../duhamel-variation-of-constants.md): the classical case of continuous forcing

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Appendix C.4, the variation of parameters formula (C.26) for $\dot\xi = A(t)\xi + \nu$ with $\nu$ locally integrable on $[\sigma_0, t]$, "verified by derivation" (p. 488), within the Carathéodory solution concept of Appendix C. The absolute-continuity argument, uniqueness and the explicit continuous-dependence bound are written out on the page.
