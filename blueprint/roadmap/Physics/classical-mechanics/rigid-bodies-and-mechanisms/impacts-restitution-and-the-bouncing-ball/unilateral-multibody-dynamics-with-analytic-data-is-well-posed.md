# Unilateral multibody dynamics with analytic data is well posed

Consider a mechanical system with configuration $q \in \mathbb{R}^d$ and the following data:
- a symmetric positive definite mass matrix $M(q)$, so the system has no massless components;
- a generalized force $f(t; q, \dot q)$;
- frictionless unilateral constraints $\phi_\alpha(q) \ge 0$ for $\alpha = 1, \dots, n$.

Let $J(q)$ be the set of active constraints, those with $\phi_\alpha(q) = 0$. Assume that at every admissible configuration $q$, one with $\phi_\alpha(q) \ge 0$ for all $\alpha$, the differentials $d\phi_\alpha(q)$ of the active constraints, $\alpha \in J(q)$, are linearly independent. Fix an impact law $\dot q^+ = F(q, \dot q^-)$ satisfying, for all $q$ and $\dot q^-$, three conditions:
- the post-impact velocity respects the active constraints: $d\phi_\alpha(q) \cdot F(q, \dot q^-) \ge 0$ for $\alpha \in J(q)$;
- there is no friction: the impulse $M(q)(F(q, \dot q^-) - \dot q^-)$ is a nonnegative combination of the $d\phi_\alpha(q)$ with $\alpha \in J(q)$;
- the kinetic energy does not increase: $F \cdot M(q) F \le \dot q^- \cdot M(q)\, \dot q^-$ with $F = F(q, \dot q^-)$.

Moreau's law with restitution coefficient $e \in [0, 1]$ is an example. An initial condition $(q_0, v_0)$ is *admissible* when $\phi_\alpha(q_0) \ge 0$ for all $\alpha$ and $d\phi_\alpha(q_0) \cdot v_0 \ge 0$ for $\alpha \in J(q_0)$. A *solution* on $[0, T]$ consists of:
- a trajectory $q$ whose velocity has bounded variation;
- nonnegative reaction measures $\lambda_\alpha$, each supported where $\phi_\alpha(q(t)) = 0$;

such that $q(0) = q_0$ and $\dot q^+(0) = v_0$, $M(q)\,\frac{D\dot q}{Dt} = f(t; q, \dot q^-) + \sum_\alpha \lambda_\alpha\,d\phi_\alpha(q)$ holds as measures, and $\dot q^+ = F(q, \dot q^-)$ at every time.

**Theorem (Ballard).**
1. Under these hypotheses, if $\phi_\alpha$, $M$ and $f$ are analytic in their arguments, then for every admissible initial condition the problem has a unique maximal solution.
2. The maximal solution is defined on a subinterval of $[0, T]$ starting at $0$ that cannot be extended. It need not reach $T$, because the solution can blow up in finite time.
3. The analyticity assumption cannot be weakened to smoothness. There are $C^\infty$ forcings for which a single particle with one constraint has several solutions.
4. The solution need not depend continuously on the initial data when a multiple impact occurs, meaning that several constraints are active at once. It does depend continuously when every multiple impact is between constraints that are orthogonal for the metric $M^{-1}(q)$, under Moreau's law.

## Background

- [For g, u₀ > 0 and 0 < e < 1, the contact times accumulate](zeno-accumulation.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Measure-differential formulation of unilateral dynamics: trajectories with velocity of bounded variation, reaction measures and contact conditions (statement prerequisite; not yet stated).
- Moreau's impact law and the admissibility, no-friction and energy requirements on impact laws (statement prerequisite; not yet stated).
- Growth and completeness conditions on $f$ and $M$, such as a global Lipschitz bound on $f$ together with uniform bounds on $M$, under which the maximal solution is defined on all of $[0, T]$ (statement prerequisite; not yet stated).
- Proof of parts 1–2 by local analytic uniqueness and continuation (proof prerequisite; not yet stated).

## Sources

- P. Ballard and A. Charles, "An overview of the formulation, existence and uniqueness issues for the initial value problem raised by the dynamics of discrete systems with unilateral contact and dry friction", *Comptes Rendus Mécanique* 346:222–236, 2018, <https://comptes-rendus.academie-sciences.fr/mecanique/item/10.1016/j.crme.2017.12.010.pdf>:
    - Section 1: Schatzman's non-uniqueness example with $C^\infty$ forcing, Percivale's analytic uniqueness, and Ballard's general result;
    - Section 4.1: the kinetic matrix $M(q)$, assumed positive definite (no massless components);
    - Section 4.2: linear independence of the active constraint differentials at every admissible configuration, the three requirements on impact laws (admissibility, no friction, no energy gain) and Moreau's law (4);
    - Section 4.3: the compatible initial condition, Problem P3, result (i) on the unique maximal solution for analytic data, defined on all of $[0, T]$ when $f$ is Lipschitz, result (ii) on discontinuous dependence at multiple impacts (Fig. 1), and Proposition 1 on continuity under $M^{-1}$-orthogonal constraints.
