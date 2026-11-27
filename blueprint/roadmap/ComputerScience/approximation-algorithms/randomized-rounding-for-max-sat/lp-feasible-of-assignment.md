# Truth assignments are feasible for the relaxation

For every truth assignment $a$, the incidence vectors $y_i = [a_i]$ and
$z_j = [a \text{ satisfies } C_j]$ are feasible for (LP), with objective $\sum_j w_j z_j$ equal to
the [weight satisfied by $a$](satisfied-weight.md). Hence the optimal value of (LP) is at least
the MAX SAT optimum, $Z^*_{LP} \ge Z^*_{IP}$.

## Sources

- M. X. Goemans and D. P. Williamson, "New 3/4-approximation algorithms for the maximum satisfiability problem", *SIAM J. Discrete Math.* 7(4) (1994), 656–666 (journal version), §3.
