# Potential method: amortized costs bound actual costs

Let costs and potentials take values in an ordered additive commutative group, and let
$a_i = t_i + \Phi(s_{i+1}) - \Phi(s_i)$ be the [amortized costs](amortized-cost.md) of a run
$s_0, s_1, \dots$ with potential $\Phi$ and actual costs $t_0, t_1, \dots$. If
$\Phi(s_0) \le \Phi(s_m)$, then

$$\sum_{i<m} t_i \le \sum_{i<m} a_i,$$

that is, the total amortized cost of the first $m$ operations is an upper bound on their total
actual cost.

## Informally uses

- [Potential method: telescoping identity](sum-cost-eq.md): the bound is the identity with the
  nonpositive term $\Phi(s_0) - \Phi(s_m)$ dropped.

## Sources

- R. E. Tarjan, *Amortized computational complexity*, SIAM J. Algebraic Discrete Methods 6(2)
  (1985) 306–318, §2.
