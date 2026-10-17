---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.EulerPolynomialFormulasWanted.eulerPolyGen_recurrence
---

# Proposition 3.2

**Proposition 3.2**: for every complex `α` and
`n ≥ 1`,
`E_n^{(α)}(x) = (x - α / 2) E_{n-1}^{(α)}(x) +
  (α / 2) ∑_{k=0}^{n-2} (n - 1 choose k) (-1)^{n-k}
  E_{n-1-k}(0) E_k^{(α)}(x)`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.EulerPolynomialFormulasWanted](../../../../../sources/v2/WantedExt.md)
- Nouara Mokhtari, Rachid Boumahdi, and Farid Bencherif, "Generalizations of Several Explicit Formulas for Euler Polynomials", Proposition 3.2.
