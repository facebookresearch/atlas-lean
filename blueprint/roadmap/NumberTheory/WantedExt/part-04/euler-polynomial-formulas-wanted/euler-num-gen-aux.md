---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.EulerPolynomialFormulasWanted.eulerNumGenAux
---

# Euler Num Gen Aux

Auxiliary fuel-bounded computation for
`eulerNumGen`: `eulerNumGenAux α fuel n` evaluates the
recurrence using values at indices at most `fuel`; it
agrees with the intended numbers whenever `n ≤ fuel`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Euler Poly](euler-poly.md)

## Sources

- [WantedExt, WantedExt.NumberTheory.EulerPolynomialFormulasWanted](../../../../../sources/v2/WantedExt.md)
