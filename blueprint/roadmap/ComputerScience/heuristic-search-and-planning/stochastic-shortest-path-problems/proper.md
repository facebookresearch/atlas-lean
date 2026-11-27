# Proper policy

In a stochastic shortest path problem with nonterminal states $S$, a deterministic stationary policy $\mu$ is proper if, from every initial state, termination has positive probability within $n = |S|$ stages: every row sum of $P_\mu^{\,n}$ is less than $1$, that is

$$\rho_\mu = \max_{s \in S} \Pr(x_n \ne t \mid x_0 = s, \mu) = \max_{s \in S} \sum_{s'} P_\mu^{\,n}(s, s') < 1.$$

A policy that is not proper is improper. With no nonterminal states every policy is proper.

## Sources

- D. P. Bertsekas, *Abstract Dynamic Programming*, 3rd ed., Athena Scientific (2022), Example 1.2.6, after Bertsekas and Tsitsiklis, Math. Oper. Res. 16 (1991).
