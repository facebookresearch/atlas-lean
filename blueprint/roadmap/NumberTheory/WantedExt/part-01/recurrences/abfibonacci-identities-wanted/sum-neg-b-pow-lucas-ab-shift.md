---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted.sum_neg_b_pow_lucasAB_shift
---

# Theorem 5(b)

**Theorem 5(b)**: for `b ≠ 0`,
(i) `∑_{i=0}^n (-b)^(n-i) L_{2(i+m)+1}
  = F_{2(n+m)+2} + (-1)^n b^(n+1) F_{2m}
  = F_{n+m+1} L_{n+m+1} + (-1)^n b^(n+1) F_m L_m` and,
for `m ≥ 1`,
(ii) `∑_{i=0}^n (-b)^(n-i) L_{2(i+m)}
  = F_{2(n+m)+1} + (-1)^n b^(n+1) F_{2m-1}
  = F_{n+m+1} L_{n+m} + (-1)^n b^(n+1) F_m L_{m-1}`.
(The middle `H`-forms of the paper are the same
equalities via its Lemma 6.)

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted](../../../../../../sources/v2/WantedExt.md)
- Emil Daniel Schwab, "Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via Unitary Convolution", Theorem 5(b).
