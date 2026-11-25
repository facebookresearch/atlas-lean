# Variation of constants for time-varying linear systems

Let $A : \mathbb{R} \to \mathbb{R}^{n \times n}$, $B : \mathbb{R} \to \mathbb{R}^{n \times m}$ and $u : \mathbb{R} \to \mathbb{R}^m$ be continuous. Let $X$ be a [fundamental matrix](fundamental-matrix-linear-system.md) of $\dot x = A(t) x$, so that $X' = A X$ and $X(t)$ is invertible for every $t$, and set $\Phi(t, s) = X(t) X(s)^{-1}$ (it does not depend on the choice of $X$). Then for all $t, s, r \in \mathbb{R}$

$$\Phi(t, t) = I, \qquad \Phi(t, s)\, \Phi(s, r) = \Phi(t, r), \qquad \partial_t \Phi(t, s) = A(t)\, \Phi(t, s),$$

and for every $t_0 \in \mathbb{R}$ and $x_0 \in \mathbb{R}^n$ the function

$$x(t) = \Phi(t, t_0)\, x_0 + \int_{t_0}^{t} \Phi(t, s)\, B(s)\, u(s) \, ds$$

satisfies $x(t_0) = x_0$ and is differentiable with $x'(t) = A(t) x(t) + B(t) u(t)$ for every $t$; every function with these two properties equals $x$. The same holds on a compact interval $[a, b] \ni t_0$ for $A$, $B$, $u$ continuous on $[a, b]$, with one-sided derivatives at the endpoints: extend the data constantly outside $[a, b]$, and note that a solution on $[a, b]$ glued at $a$ and $b$ with the solutions of the extended problem is a solution on $\mathbb{R}$.

The formula is checked by differentiating under the integral sign; for uniqueness, the difference $d$ of two solutions satisfies $d' = A(t) d$ and $d(t_0) = 0$, so $d = 0$ by uniqueness for the homogeneous equation. For constant $A$, $\Phi(t, s) = e^{(t - s)A}$ and the formula is [Duhamel's formula](../duhamel-variation-of-constants.md).

## Depends on

- [Fundamental matrix of a linear system](fundamental-matrix-linear-system.md): the fundamental matrix $X$ defining $\Phi$.

## Proof depends on

- [Fundamental matrix of a linear system](fundamental-matrix-linear-system.md): uniqueness of solutions of the homogeneous equation.

## Background

- [Duhamel's formula (variation of constants)](../duhamel-variation-of-constants.md): the time-invariant case.

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Appendix C.4: the fundamental solution (C.24), the variation of parameters formula (C.26) and Lemma/Exercise C.4.1(a)–(b) (pp. 487–488), stated there for measurable locally essentially bounded $A$ and locally integrable forcing, which contain the continuous case above.
