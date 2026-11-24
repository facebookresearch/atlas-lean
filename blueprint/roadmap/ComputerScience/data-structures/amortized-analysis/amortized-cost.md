# Amortized cost of an operation

Let $S$ be a type of configurations, $R$ an additive commutative group, $\Phi : S \to R$ a
potential, $s_0, s_1, s_2, \dots$ a run of configurations and $t_0, t_1, \dots \in R$ the actual
costs of its operations, operation $i$ taking $s_i$ to $s_{i+1}$. The amortized cost of
operation $i$ is

$$a_i = t_i + \Phi(s_{i+1}) - \Phi(s_i).$$

The actual cost $t_i$ is whatever the client's cost model counts (rotations, pointer changes,
unit-cost steps); nothing here fixes a machine model.

## Sources

- R. E. Tarjan, *Amortized computational complexity*, SIAM J. Algebraic Discrete Methods 6(2)
  (1985) 306–318, §2 (the physicist's view, credited there to D. Sleator).
