# The Luby restart sequence

The **Luby sequence** $(t_i)_{i \ge 1}$ is defined by

$$
t_i = \begin{cases} 2^{k-1} & \text{if } i = 2^k - 1, \\ t_{\,i - 2^{k-1} + 1} & \text{if } 2^{k-1} \le i < 2^k - 1, \end{cases}
$$

giving $1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, \dots$: each complete prefix of length $2^k - 1$ is repeated once and followed by $2^k$. A CDCL solver with Luby restarts and unit $u \ge 1$ restarts after $u \cdot t_i$ conflicts in its $i$-th run.

## Sources

- M. Luby, A. Sinclair and D. Zuckerman, "Optimal Speedup of Las Vegas Algorithms", Information Processing Letters 47(4), 1993, Section 3: the universal strategy.
- J. Huang, "The Effect of Restarts on the Efficiency of Clause Learning", Proceedings of the 20th International Joint Conference on Artificial Intelligence (IJCAI 2007), 2007, Section 3.1: Luby restarts in a clause-learning solver, with this recursive definition and unit $32$.
