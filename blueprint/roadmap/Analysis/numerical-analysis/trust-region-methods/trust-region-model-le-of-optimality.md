# Sufficient optimality condition for the trust-region subproblem

Let $B$ be symmetric, $\mu \ge 0$, and suppose

$$(B + \mu I) s = -g, \qquad B + \mu I \succeq 0, \qquad \mu\, (\Delta - \|s\|) = 0 .$$

Then $q(s) \le q(p)$ for every $p$ with $\|p\| \le \Delta$, where
$q(p) = g^\top p + \tfrac12 p^\top B p$ is the [quadratic model](trust-region-model.md); so if also
$\|s\| \le \Delta$, then $s$ is a global minimiser of the trust-region subproblem, even when $B$ is
indefinite. This is the sufficiency half of the characterisation of global solutions due to Gay and
to Moré and Sorensen; for the
converse see the [necessity half](exists-optimality-of-is-min-on.md).

Proof: expanding with $g = -(B + \mu I) s$ gives

$$q(p) - q(s) = \tfrac12 (p - s)^\top (B + \mu I)(p - s) + \tfrac{\mu}{2} \bigl(\|s\|^2 - \|p\|^2\bigr),$$

and complementarity makes $\mu \|s\|^2 = \mu \Delta^2 \ge \mu \|p\|^2$.

## Sources

- N. I. M. Gould, D. P. Robinson and H. S. Thorne, *On solving trust-region and other regularised subproblems in optimization*, Math. Program. Comput. 2 (2010); https://www.cs.ox.ac.uk/files/2182/NA-09-01.pdf, Theorem 2.1 (necessity, with the identity as norm matrix; that source credits the
  characterisation to Gay (1981) and to Moré and Sorensen (1983)); this page proves the converse.
