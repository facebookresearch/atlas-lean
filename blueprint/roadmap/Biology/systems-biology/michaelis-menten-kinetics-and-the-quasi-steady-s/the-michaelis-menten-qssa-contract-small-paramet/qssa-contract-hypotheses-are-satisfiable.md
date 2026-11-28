# The hypotheses of the QSSA contract are satisfiable

For positive rate constants, initial substrate and enzyme, a reduced solution exists on every slow-time window and the full system has a solution on the matching real-time window with the standard data. So the QSSA contract constrains actual trajectories and is not vacuous.

Let $k_1 > 0$, $k_b \ge 0$, $k_2 > 0$, $s_0 > 0$, $e_0 > 0$ and $T$ real, with
$K_M = (k_b + k_2)/k_1$, $\kappa = K_M/s_0$ and the [slow time scale](slow-time-scale.md)
$t_S = (s_0 + K_M)/(k_2 e_0)$. Then

1. there is $u : \mathbb{R} \to \mathbb{R}$ that [solves the reduced problem](is-reduced-solution-on.md)
   on $[0, T]$, with $u > 0$ on $[0, \infty)$; and
2. there are $s, c : \mathbb{R} \to \mathbb{R}$ that
   [solve the system on the window](is-solution-on.md) $[0, t_S T]$ with total enzyme $e_0$ and the
   standard data $s(0) = s_0$, $c(0) = 0$; they can be chosen with $s > 0$ and $0 \le c \le e_0$ on
   $[0, t_S T]$.

For $T > 0$ the window $[0, t_S T]$ has positive length, so every $\delta \in (0, T]$ yields a
genuine instance of both clauses of the
[QSSA contract](qssacontract.md).

## Depends on

- [Slow time scale of substrate depletion](slow-time-scale.md)
- [Solution of the reduced problem on a slow-time window](is-reduced-solution-on.md)
- [Solution of the Michaelis–Menten system on a time window](is-solution-on.md)

## Proof depends on

- [For K > 0 a positive reduced solution passes through every s₀ > 0](../exists-reduced-solution.md)
- [Global nonnegative trajectories exist from nonnegative data](../global-positive-trajectories-of-the-michaelis-me/exists-is-solution-nonneg.md)
- [A global solution solves the system on every window](is-solution-on-2.md)
- [Reduced vector field in slow time](reduced-field.md)

## Expansion

For (1), take the positive solution $\bar S$ of $\bar S' = -k_2\bar S/(K_M + \bar S)$ through $s_0$
(it exists because $K_M > 0$) and set $u(\theta) = \bar S((s_0 + K_M)\theta/k_2)/s_0$; the chain rule
and $(s_0 + K_M)/s_0 = 1 + \kappa$ give $u' = -(1 + \kappa)u/(\kappa + u)$, the reduced field, at
every $\theta$, and $u(0) = 1$.

For (2), take the global nonnegative solution $(s, c, e, p)$ with data $(s_0, 0, e_0, 0)$. Its total
enzyme $e + c$ stays $e_0$, so $c \le e_0$; $s$ starts positive and stays positive. A global solution
with $e(0) + c(0) = e_0$ is a window solution on every window, in particular on $[0, t_S T]$.

## Sources

- J. Eilertsen, S. Schnell and S. Walcher, "Rigorous estimates for the quasi-steady state approximation
  of the Michaelis–Menten reaction mechanism at low enzyme concentrations", *Nonlinear Analysis: Real World Applications* 78 (2024), 104088, <https://doi.org/10.1016/j.nonrwa.2024.104088>; locators from the version read, arXiv:2305.12602v2 (2024),
  Section 1, Eqs. (1) and (2) with initial values $s(0) = s_0$, $c(0) = 0$,
  <https://arxiv.org/abs/2305.12602v2>.
