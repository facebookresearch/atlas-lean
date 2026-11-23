# Potential method: telescoping identity

For every potential $\Phi$, run $s_0, s_1, \dots$ and actual costs $t_0, t_1, \dots$, with
amortized costs $a_i = t_i + \Phi(s_{i+1}) - \Phi(s_i)$, and for every $m \ge 0$,

$$\sum_{i<m} t_i = \sum_{i<m} a_i + \Phi(s_0) - \Phi(s_m).$$

The total actual cost equals the total amortized cost plus the net decrease in potential from
the initial to the final configuration. The proof is the telescoping of the potential terms.

## Background

- [Amortized cost of an operation](amortized-cost.md): the definition of $a_i$.

## Sources

- R. E. Tarjan, *Amortized computational complexity*, SIAM J. Algebraic Discrete Methods 6(2)
  (1985) 306–318, §2, the displayed identity.
- D. D. Sleator and R. E. Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)
  652–686, §2.
