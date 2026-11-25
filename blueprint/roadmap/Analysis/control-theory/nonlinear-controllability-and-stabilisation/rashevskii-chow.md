# Rashevskii–Chow theorem

Let $\Omega$ be a connected nonempty open subset of a finite-dimensional real normed space $E$ and $f_1, \dots, f_m$ vector fields of class $C^\infty$ on $\Omega$ such that the Lie algebra rank condition holds at every point of $\Omega$. Then for all $x_0, x_1 \in \Omega$ and every $T > 0$ there are a bounded measurable control $u : [0, T] \to \mathbb{R}^m$ and a continuous trajectory $x : [0, T] \to \Omega$ of the driftless system $\dot x = \sum_i u_i f_i(x)$, in the Carathéodory sense $x(t) = x_0 + \int_0^t \sum_i u_i(s) f_i(x(s)) \, ds$, with $x(0) = x_0$ and $x(T) = x_1$.

This is Coron, *Control and Nonlinearity* (AMS 2007), Theorem 3.18, proved independently by Rashevskii (1938) and Chow (1939). Coron's controls are in $L^\infty((0, T); \mathbb{R}^m)$; the statement asks for a measurable control bounded on $[0, T]$, the same class. Since the fields are continuous on $\Omega$ and the trajectory stays in $\Omega$, the integrand is integrable and the integral equation is the usual notion of solution. Coron's proof also gives small-time local controllability at every point of $\Omega$ (Theorem 3.19), which is not part of the statement above. Its hypotheses hold for the nonholonomic integrator on $\Omega = \mathbb{R}^3$.

## Background

- [Accessibility space of a driftless system at a point](accessibility-space.md): the hypothesis is that it is the whole space at every point of $\Omega$.
- [The nonholonomic integrator satisfies the Lie algebra rank condition](accessibility-space-nonholonomic-fields.md): Coron's Example 3.20, a driftless system on $\mathbb{R}^3$ with two controls whose bracket $[f_1, f_2]$ supplies the third direction.
