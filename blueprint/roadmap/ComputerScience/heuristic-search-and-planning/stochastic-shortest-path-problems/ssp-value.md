# Value of a stationary policy in a stochastic shortest path problem

The value of a stationary policy $\mu$ in a stochastic shortest path problem is the limit, as $N \to \infty$, of its $N$-stage total rewards $T_\mu^N 0$, where $T_\mu$ is the undiscounted ($\gamma = 1$) Bellman operator of $\mu$ (an unspecified function when this limit does not exist). For a proper policy of a substochastic MDP the limit exists, is the unique fixed point of $T_\mu$, and equals the total expected reward until termination $\sum_{k \ge 0} P_\mu^k r_\mu$. Bertsekas's cost of $\mu$ is the negative of this value.

## Sources

- D. P. Bertsekas, *Abstract Dynamic Programming*, 3rd ed., Athena Scientific (2022), Section 1.2.1 (the cost $J_\pi$ of a policy as a limit of $N$-stage costs) and Example 1.2.6.
