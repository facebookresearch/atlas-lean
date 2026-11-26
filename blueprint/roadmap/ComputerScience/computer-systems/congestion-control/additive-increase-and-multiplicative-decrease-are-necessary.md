# Additive increase and multiplicative decrease are necessary

Consider [linear controls](linear-increase-decrease-controls.md) with parameters $a_I, a_D \in \mathbb R$ and $b_I, b_D > 0$, applied without truncation, and require, for every number of users $n \ge 1$ and every allocation $x \in [0, \infty)^n$:

1. (nonnegativity) both steps keep every load nonnegative, that is $a_I \ge 0$ and $a_D \ge 0$;
2. (distributed convergence to efficiency) each user moves in the direction the feedback asks, whatever the others do: $a_I + b_I x_i > x_i$ and $a_D + b_D x_i < x_i$ for every load $x_i > 0$;
3. (convergence to fairness) for $x \ne 0$, neither step decreases the [fairness index](jain-s-fairness-index.md), and when $F(x) < 1$ at least one of the two steps increases it.

These requirements hold if and only if

$$
a_I > 0, \qquad b_I \ge 1, \qquad a_D = 0, \qquad 0 < b_D < 1 .
$$

That is, the decrease must be multiplicative, and the increase must have an additive component and optionally a multiplicative one with coefficient at least one. In particular additive increase with multiplicative decrease ($b_I = 1$) qualifies, while additive increase with additive decrease ($a_D < 0$) and multiplicative increase with multiplicative decrease ($a_I = 0$) do not.

**Proof.** Letting $x_i \to 0^+$ in requirement 2 for the decrease gives $a_D \le 0$, hence $a_D = 0$ by requirement 1, and then $b_D < 1$. Requirement 2 for the increase, $a_I + (b_I - 1)x_i > 0$ for all $x_i > 0$, gives $b_I \ge 1$ by letting $x_i \to \infty$. By [fairness after one step of a linear control](fairness-after-one-step-of-a-linear-control.md), a step with $a \ge 0$ never decreases fairness and increases the fairness of an unfair allocation exactly when $a > 0$; since $a_D = 0$, requirement 3 forces $a_I > 0$. Conversely these parameters satisfy all three requirements.

## Depends on

- [Linear increase/decrease controls](linear-increase-decrease-controls.md)
- [Jain's fairness index](jain-s-fairness-index.md)

## Proof depends on

- [Fairness after one step of a linear control](fairness-after-one-step-of-a-linear-control.md)

## Sources

- D.-M. Chiu and R. Jain, "Analysis of the increase and decrease algorithms for congestion avoidance in computer networks", *Computer Networks and ISDN Systems* 17(1):1–14, 1989, Sections 2.2–2.4: equation (3) (efficiency), equations (8)–(10) (fairness and nonnegativity, where $b_D = 0$ is also admitted), equations (11)–(12) (distributed efficiency) and Proposition 1.
