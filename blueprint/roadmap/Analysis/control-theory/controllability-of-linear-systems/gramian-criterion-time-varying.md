# Gramian criterion for controllability of time-varying linear systems

Let $A : \mathbb{R} \to \mathbb{R}^{n \times n}$ and $B : \mathbb{R} \to \mathbb{R}^{n \times m}$ be continuous, let $\Phi(t, s)$ be the [transition matrix](../../ordinary-differential-equations/linear-systems-and-fundamental-matrices/variation-of-parameters-time-varying.md) of $\dot x = A(t) x$, and consider $\dot x = A(t) x + B(t) u$ with continuous controls $u : [\sigma, \tau] \to \mathbb{R}^m$, whose solutions are given by the [variation of constants formula](../../ordinary-differential-equations/linear-systems-and-fundamental-matrices/variation-of-parameters-time-varying.md). For $\sigma < \tau$ the system is **controllable on $[\sigma, \tau]$** if every state at time $\sigma$ can be steered to every state at time $\tau$. Write $b_i(s)$ for the $i$-th column of $B(s)$. The following are equivalent:

1. the system is controllable on $[\sigma, \tau]$;
2. the matrix $W(\sigma, \tau) = \int_\sigma^\tau \Phi(\tau, s) B(s) B(s)^\top \Phi(\tau, s)^\top \, ds$ is positive definite;
3. there is no nonzero $p \in \mathbb{R}^n$ with $p^\top \Phi(\tau, s) b_i(s) = 0$ for every $s \in [\sigma, \tau]$ and every $i$.

If these hold, then for all states $x, z$ the control

$$u(t) = B(t)^\top \Phi(\tau, t)^\top W(\sigma, \tau)^{-1} \big(z - \Phi(\tau, \sigma) x\big)$$

is continuous, steers $x$ at time $\sigma$ to $z$ at time $\tau$, and is the unique continuous control of smallest $L^2$ norm $\big(\int_\sigma^\tau \|u\|^2\big)^{1/2}$ among the continuous controls doing so.

Sontag proves the equivalence for measurable, essentially bounded coefficients and controls, with the minimum-norm control unique up to equality almost everywhere. For continuous $A$, $B$ the displayed control is continuous, so controllability with continuous controls is equivalent to controllability with essentially bounded ones; continuous functions that agree almost everywhere agree everywhere, and in condition 3 vanishing almost everywhere is vanishing everywhere.

## Depends on

- [Variation of constants for time-varying linear systems](../../ordinary-differential-equations/linear-systems-and-fundamental-matrices/variation-of-parameters-time-varying.md): the transition matrix $\Phi$.

## Proof depends on

- [Variation of constants for time-varying linear systems](../../ordinary-differential-equations/linear-systems-and-fundamental-matrices/variation-of-parameters-time-varying.md): the endpoint $\Phi(\tau, \sigma) x + \int_\sigma^\tau \Phi(\tau, s) B(s) u(s)\, ds$ of a controlled trajectory.

## Background

- [Gramian criterion for controllability](is-controllable-on-iff-bijective-gramian.md): the time-invariant case, $\Phi(\tau, s) = e^{(\tau - s) A}$.

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 3.5: Proposition 3.5.4 and Theorem 5, with the reduction to the operator $\omega \mapsto \int_\sigma^\tau \Phi(\tau, s) B(s) \omega(s)\, ds$ that precedes it (pp. 107–109).
