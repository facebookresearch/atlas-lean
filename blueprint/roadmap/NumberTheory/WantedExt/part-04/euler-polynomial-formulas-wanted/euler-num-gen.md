---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.EulerPolynomialFormulasWanted.eulerNumGen
---

# Euler Num Gen

The order-`α` Euler numbers `E_k^{(α)}(0)`, defined
by `E_0^{(α)}(0) = 1` and
`E_{n+1}^{(α)}(0) = -α E_n^{(α)}(0) +
  (α / 2) ∑_{k=0}^n (n choose k) E_k^{(α)}(0) E_{n-k}(0)`,
the coefficient recurrence of the generating function
`(2 / (e^t + 1))^α` (computed here through the
fuel-bounded `eulerNumGenAux`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Euler Num Gen Aux](euler-num-gen-aux.md)

## Sources

- [WantedExt, WantedExt.NumberTheory.EulerPolynomialFormulasWanted](../../../../../sources/v2/WantedExt.md)
- Nouara Mokhtari, Rachid Boumahdi, and Farid Bencherif, "Generalizations of Several Explicit Formulas for Euler Polynomials", Section 1 (generalized Euler polynomials).
