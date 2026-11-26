# Leading coefficient of a polynomial from its values at distinct nodes

Let $F$ be a field, let $s$ be a finite set with $m \ge 1$ elements, and let $v : s \to F$ be injective. For every polynomial $P$ over $F$ of degree less than $m$, the coefficient of $X^{m-1}$ in $P$ is

$$\sum_{i \in s} \frac{P(v_i)}{\prod_{j \in s,\ j \ne i} (v_i - v_j)} .$$

It follows from writing $P$ as its Lagrange interpolant at the nodes $v_i$ and reading off the coefficient of $X^{m-1}$ in each Lagrange basis polynomial.

## Sources

- Mathlib, `Lagrange.coeff_eq_sum` in `Mathlib/LinearAlgebra/Lagrange.lean`. <https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Lagrange.lean>
