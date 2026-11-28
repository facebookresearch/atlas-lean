# Window solutions of the Michaelis–Menten system are unique

Two solutions of the Michaelis–Menten system on a time window $[0, t_1]$, $t_1 \ge 0$, with the same total enzyme and the same initial substrate and complex agree on the whole window. Whenever a global solution with these data exists, the window solution agrees with its restriction.

For real $k_1, k_b, k_2, e_0$ and $t_1 \ge 0$, let $(s, c)$ and $(\tilde s, \tilde c)$ both be
[solutions of the Michaelis–Menten system on the window](is-solution-on.md) $[0, t_1]$ with total
enzyme $e_0$: at every $t \in [0, t_1]$ both pairs have two-sided derivatives with

$$s' = -k_1 (e_0 - c)\, s + k_b c, \qquad c' = k_1 (e_0 - c)\, s - (k_b + k_2)\, c,$$

and likewise for $(\tilde s, \tilde c)$. If $s(0) = \tilde s(0)$ and $c(0) = \tilde c(0)$, then
$s(t) = \tilde s(t)$ and $c(t) = \tilde c(t)$ for every $t \in [0, t_1]$. No sign condition on the
rate constants or the data is needed.

In particular, let $(s, c, e, p)$ be a global [solution](../is-solution.md) of the Michaelis–Menten
mass-action system with $e(0) + c(0) = e_0$. Every window solution $(\tilde s, \tilde c)$ with total
enzyme $e_0$, $\tilde s(0) = s(0)$ and $\tilde c(0) = c(0)$ coincides with $(s, c)$ on $[0, t_1]$,
because the global solution is itself a
[window solution on every window](is-solution-on-2.md). This identifies a window solution with an
independently supplied global solution; uniqueness alone does not prove global existence for arbitrary real data.

## Depends on

- [Solution of the Michaelis–Menten system on a time window](is-solution-on.md)
- [Solution of the Michaelis–Menten mass-action system](../is-solution.md)

## Proof depends on

- [Solution of the Michaelis–Menten system on a time window](is-solution-on.md)
- [A global solution solves the system on every window](is-solution-on-2.md)
- [Tube bootstrap for perturbed trajectories](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/tube-bootstrap.md)

## Expansion

Write $x = (s, c)$ and $F(x) = (-k_1 (e_0 - c) s + k_b c,\ k_1 (e_0 - c) s - (k_b + k_2) c)$, an
autonomous polynomial field on $\mathbb{R}^2$. Both curves are differentiable, hence continuous, on
the compact window, so they lie in a bounded set; a polynomial field is Lipschitz with some constant
$K$ on the closed ball of radius $r = 1$ around that bounded set. Apply the tube bootstrap with
$f = (s, c)$, $g = (\tilde s, \tilde c)$, $T = t_1$, perturbation size $0$ and initial distance $0$:
the Gronwall bound is $G \equiv 0 < r$, so $\|f(t) - g(t)\| \le 0$ on $[0, t_1]$. For $t_1 = 0$ the
claim is the initial condition.

The window form matters for the QSSA contract, whose solutions are assumed only on
$[0, t_S T]$: the global estimates of the substrate and of the complex apply to a window solution only
after this identification.

## Sources

- G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, Graduate Studies in
  Mathematics 140, American Mathematical Society (2012), Theorem 2.2 (Picard–Lindelöf) and the
  opening uniqueness argument of Section 2.6, pp. 38 and 50–51 in the
  [author's preliminary version](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf).
  Apply local uniqueness to the autonomous polynomial field $F$ above; the continuation
  argument extends equality to the common window, with its endpoints handled by continuity.
  The global-solution specialization is also the [equality from initial data](../global-positive-trajectories-of-the-michaelis-me/eq-of-initial.md).
- Model background: J. Eilertsen, S. Schnell and S. Walcher, "Rigorous estimates for the quasi-steady state approximation
  of the Michaelis–Menten reaction mechanism at low enzyme concentrations", *Nonlinear Analysis: Real World Applications* 78 (2024), 104088, <https://doi.org/10.1016/j.nonrwa.2024.104088>; locators from the version read, arXiv:2305.12602v2 (2024),
  Section 1, Eq. (1) (the system in the variables $s, c$ with $e = e_0 - c$ and data $s(0) = s_0$,
  $c(0) = 0$), <https://arxiv.org/abs/2305.12602v2>.
