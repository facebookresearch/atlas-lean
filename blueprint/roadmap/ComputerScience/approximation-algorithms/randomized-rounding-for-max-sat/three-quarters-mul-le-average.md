# Goemans–Williamson Theorem 4.1, per clause

For a clause $C$ whose literals use distinct variables, $0 \le y_i \le 1$ on its variables and
$0 \le z \le \min\left(1, \sum_{i \in P} y_i + \sum_{i \in N}(1 - y_i)\right)$,

$$\frac{\Pr_{1/2}[C] + \Pr_y[C]}{2} \ge \frac34 z ,$$

where $\Pr_{1/2}$ is the probability that Johnson's assignment satisfies $C$ and $\Pr_y$ the
probability that randomized rounding does.
The empty clause is covered: then $z = 0$.

## Informally uses

- [Johnson's random assignment](clause-sat-prob-half.md), [Lemma 3.1](rounding-factor-mul-le-clause-sat-prob.md)
  and [the per-clause inequality](three-halves-le-johnson-add-rounding-fac.md).

## Sources

- M. X. Goemans and D. P. Williamson, "New 3/4-approximation algorithms for the maximum satisfiability problem", *SIAM J. Discrete Math.* 7(4) (1994), 656–666 (journal version), proof of Theorem 4.1.
