# Robust Scheffé test between two distributions

Let $q_0, q_1$ be distributions on a finite set $X$, let $A = \{x : q_1(x) < q_0(x)\}$ be their *Scheffé set* (so $q_0(A) - q_1(A) = d_{TV}(q_0,q_1)$, where $d_{TV}(\mu,\nu) = \max_B |\mu(B) - \nu(B)|$), and let $\hat\mu_n(A)$ be the fraction of the sample $x_1, \dots, x_n$ lying in $A$. The *Scheffé test* favors $q_0$ iff $\hat\mu_n(A) \ge (q_0(A) + q_1(A))/2$. If the sample is i.i.d. from an arbitrary distribution $p$ with $d_{TV}(p, q_0) + \gamma \le d_{TV}(q_0, q_1)/2$ for some $\gamma \ge 0$, then the test favors $q_1$ with probability at most $e^{-2n\gamma^2}$.

## Proof sketch

Under $p$ the mean of $\hat\mu_n(A)$ is $p(A) \ge q_0(A) - d_{TV}(p,q_0)$, which exceeds the midpoint by at least $\gamma$ under the hypothesis. Favoring $q_1$ requires the empirical mean to fall at least $\gamma$ below its expectation, and Hoeffding's inequality bounds this by $e^{-2n\gamma^2}$.

## Depends on

- [Total variation distance between finite measures](../../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- Luc Devroye and Gábor Lugosi, "Combinatorial Methods in Density Estimation", Springer, 2001.
