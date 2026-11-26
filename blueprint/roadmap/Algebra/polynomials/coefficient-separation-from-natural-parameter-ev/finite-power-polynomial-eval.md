# Evaluation is the finite scalar power sum

For `N : ℕ`, `a : Fin N → ℚ`, and `x : ℚ`, `(finitePowerPolynomial N a).eval x = ∑ i : Fin N,
a i * x^i.val`.
