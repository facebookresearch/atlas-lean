# Scheffé tournament selects a 3-approximate hypothesis in total variation

Let $q_1, \dots, q_M$ be distributions on a finite set, and let the sample $x_1, \dots, x_n$ be i.i.d. from an arbitrary $p$ (not necessarily in the family). For each candidate $i$ let its score be $\max_j |\hat\mu_n(A_{j,i}) - q_i(A_{j,i})|$, where $A_{j,i} = \{x : q_i(x) < q_j(x)\}$ and $\hat\mu_n$ is the empirical distribution, and let $\hat q$ be a candidate of minimal score. Then for every $\gamma \ge 0$, with probability at least $1 - 2M(M-1)e^{-2n\gamma^2}$,

$$
d_{TV}(p, \hat q) \le 3\, d_{TV}(p, q_i) + 2\gamma \quad \text{simultaneously for all } i.
$$

## Proof sketch

By Hoeffding and a union bound over the at most $M(M-1)$ Scheffé sets (two tails each), all empirical masses are within $\gamma$ of $p$ simultaneously with the stated probability. On that event every score is within $\gamma$ of the corresponding population discrepancy, and the triangle inequality for total variation along the Scheffé set separating $\hat q$ and $q_i$ gives the factor $3$.

## Depends on

- [Total variation distance between finite measures](../../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Robust Scheffé test between two distributions](robust-scheffe-test.md)
- [Hoeffding's inequality for averages of bounded variables](../../../concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- Luc Devroye and Gábor Lugosi, "Combinatorial Methods in Density Estimation", Springer, 2001.
