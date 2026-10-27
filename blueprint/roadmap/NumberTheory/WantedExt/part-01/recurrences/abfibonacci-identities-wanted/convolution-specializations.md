---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted.convolution_specializations
---

# Corollary 14(b)

**Corollary 14(b)**: the specializations
(i) `∑_{i=1}^n L_{n-i} J_i = j_{n+1} - L_{n+1}
  = ∑_{i=1}^n j_{n-i} F_i` (Fibonacci/Jacobsthal),
(ii) `2 ∑_{i=1}^n P_i = (Q_{n+1} - 2) / 2
  = ∑_{i=1}^n i Q_{n-i}` (Pell), and
(iii) `∑_{i=1}^n L_{2(n-i)} (2^i - 1)
  = L_{2n+2} - 2^(n+1) - 1
  = ∑_{i=1}^n (2^(n-i) + 1) F_{2i}` (Fibonacci).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted](../../../../../../sources/v2/WantedExt.md)
- Emil Daniel Schwab, "Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via Unitary Convolution", Corollary 14(b).
