# An upper bound for the curvature integral depending only on the constraint matrix

First question: for all $m, n$ and every real $m \times n$ matrix $A$ of rank $m$, there is a real $K$ (depending
on $A$) such that for all $b \in \mathbb{R}^m$ and $c \in \mathbb{R}^n$ satisfying the
[standing assumptions](standing-assumptions.md), and all paths $x, s : \mathbb{R} \to \mathbb{R}^n$ and
$y : \mathbb{R} \to \mathbb{R}^m$ whose value at every $\nu > 0$ is a
[central-path point](is-central-path-point.md) with parameter $\nu$, the curvature integral satisfies
$F(\infty, 0) = \int_0^\infty \kappa(\nu)/\nu \, d\nu \le K$, with $\kappa$ the
[curvature](curvature.md). This is one finite bound for all admissible right-hand sides $b$ and costs $c$;
it does not say that the integral is the same for all of them. The integral is the Lebesgue integral of a
nonnegative function in $[0, \infty]$, so no finiteness is presupposed.

Its resolution: [The curvature integral of the central path is bounded in terms of the constraint matrix](curvature-integral-bounded-by-a-holds.md).
