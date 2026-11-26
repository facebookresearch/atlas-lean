# Coefficient of index m − 1 of a polynomial of degree below m from its values at m distinct nodes

Let $F$ be a field, let $s$ be a finite set with $m$ elements ($m = 0$ allowed), and let $v : s \to F$ be injective. For every polynomial $P$ over $F$ of degree less than $m$, the coefficient of $X^{m \mathbin{\dot-} 1}$ in $P$ is

$$\sum_{i \in s} \frac{P(v_i)}{\prod_{j \in s,\ j \ne i} (v_i - v_j)} .$$

Here $m \mathbin{\dot-} 1$ is truncated subtraction, so for $m = 0$ the index is $0$; then $P = 0$ and both sides are $0$. The coefficient is the leading one only when $\deg P = m - 1$: for the nodes $0, 1$ and $P = 1$ the sum is $-1 + 1 = 0$, the coefficient of $X^1$. The identity follows from writing $P$ as its Lagrange interpolant at the nodes $v_i$ and reading off the coefficient of $X^{m-1}$ in each Lagrange basis polynomial.

## Sources

- Mathlib, `Lagrange.coeff_eq_sum` in `Mathlib/LinearAlgebra/Lagrange.lean`. <https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Lagrange.lean>
