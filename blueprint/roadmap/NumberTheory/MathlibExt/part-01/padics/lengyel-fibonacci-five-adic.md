---
article_id: af_544f2994058ed20e13408eda
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.lengyel_fibonacci_five_adic
---

# Fibonacci Five Adic Valuation

5-adic valuation of Fibonacci numbers: for `1 ≤ n`,
`padicValNat 5 (Nat.fib n) = padicValNat 5 n`.

Provenance: Fatehizadeh–Yaqubi, Lemma `Leg1`, citing Lengyel (1995).
The source prints `n ≥ 0`, but its p-adic valuation is defined for positive
integers, so this formalizes the audited `1 ≤ n` restriction. Only the 5-adic
clause is formalized; the source's separate 2-adic and 3-adic clauses are out
of scope.
Proves `Wanted` entry `lengyel_fibonacci_five_adic`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Padics.FibonacciFiveAdicValuation](../../../../../sources/v2/MathlibExt.md)
