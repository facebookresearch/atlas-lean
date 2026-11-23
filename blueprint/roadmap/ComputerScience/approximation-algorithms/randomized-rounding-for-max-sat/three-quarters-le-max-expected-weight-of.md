# The 3/4 guarantee against the MAX SAT optimum

For clauses on distinct variables and nonnegative weights, if $(y, z)$ is an optimal solution of
(LP), then for every truth
assignment $a$,

$$\max(\hat W_1, \hat W_2) \ge \frac34 \sum_{j : a \models C_j} w_j .$$

Here $\hat W_1$, $\hat W_2$ are the [expected weights](expected-weight.md) of Johnson's assignment
and of randomized rounding, so the better of the two has expected weight at least $\frac34$ of the
optimum. Distinct variables matter: for the single clause $x_0 \vee x_0$ of weight $1$,
$y_0 = \frac12$, $z = 1$ is optimal for the relaxation (which counts the literal twice), yet both
roundings satisfy the clause with probability $\frac12$. Derandomization by conditional
probabilities turns this into a deterministic $\frac34$-approximation algorithm.

## Informally uses

- [Theorem 4.1](three-quarters-le-max-expected-weight.md) and
  [feasibility of truth assignments](lp-feasible-of-assignment.md).

## Sources

- M. X. Goemans and D. P. Williamson, "New 3/4-approximation algorithms for the maximum satisfiability problem", *SIAM J. Discrete Math.* 7(4) (1994), 656–666 (journal version), Theorem 4.1 with $Z^*_{LP} \ge Z^*_{IP}$ (§3).
