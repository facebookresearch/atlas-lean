# The Luby restart sequence

The **Luby sequence** $(t_i)_{i \ge 1}$ is defined by

$$
t_i = \begin{cases} 2^{k-1} & \text{if } i = 2^k - 1, \\ t_{\,i - 2^{k-1} + 1} & \text{if } 2^{k-1} \le i < 2^k - 1, \end{cases}
$$

giving $1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, \dots$: each complete prefix of length $2^k - 1$ is repeated once and followed by $2^k$. With base $y$ in place of $2$, a CDCL solver restarts after $u \cdot t_i$ conflicts in its $i$-th run, for a unit $u$.

## Depends on

- [Las Vegas and Monte Carlo algorithms](../../randomized-algorithms/probabilistic-analysis-tools/las-vegas-and-monte-carlo-algorithms.md)

## Sources

- M. Luby, A. Sinclair and D. Zuckerman, "Optimal Speedup of Las Vegas Algorithms", Information Processing Letters 47(4), 1993.
- N. Eén and N. Sörensson, "An Extensible SAT-solver", Theory and Applications of Satisfiability Testing (SAT 2003), LNCS 2919, Springer, 2004.
