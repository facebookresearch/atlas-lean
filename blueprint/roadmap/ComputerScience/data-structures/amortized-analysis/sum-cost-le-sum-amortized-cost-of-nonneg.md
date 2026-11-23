# Potential method with a nonnegative potential that starts at zero

Let costs and potentials take values in an ordered additive commutative group, and let
$a_i = t_i + \Phi(s_{i+1}) - \Phi(s_i)$ be the [amortized costs](amortized-cost.md) of a run
$s_0, s_1, \dots$ with potential $\Phi$ and actual costs $t_0, t_1, \dots$. If $\Phi(s_0) = 0$ and
$\Phi(s_i) \ge 0$ for every $i$, then for every $m$

$$\sum_{i<m} t_i \le \sum_{i<m} a_i.$$

This is the situation Tarjan singles out as the common one ("the initial potential is zero and
the potential is always nonnegative"); it corresponds to the banker's view of amortization in
which credits are never borrowed. For instance, a stack whose potential is its size starts at
zero, and an operation popping $k$ items and pushing one has amortized cost $2$, so $m$ such
operations perform at most $2m$ pushes and pops.

## Informally uses

- [Potential method: amortized costs bound actual costs](sum-cost-le-sum-amortized-cost.md):
  applied with $\Phi(s_0) = 0 \le \Phi(s_m)$.

## Background

- [Stack with multipop](../linear-structures/stack-with-multipop/README.md): the stack example
  of Tarjan's §1–2, treated there with its own cost model.

## Sources

- R. E. Tarjan, *Amortized computational complexity*, SIAM J. Algebraic Discrete Methods 6(2)
  (1985) 306–318, §2.
