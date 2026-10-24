---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.PrimitiveNondeficientWanted.max_primeFactor_lt_sqrt_radical_or_exists_pow_lt
---

# Proposition

**Proposition** (dichotomy): if `n` is an odd primitive
non-deficient number with least prime factor `p₁`, greatest prime
factor `p_k`, `k` distinct prime factors, and radical `R`, then
either `p_k < √R` or some prime factor `p` satisfies
`p^(a+1) < (k + 2 + p₁)(p_k - 1)`, where `a` is the exponent
of `p`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.PrimitiveNondeficientWanted](../../../../../sources/v2/WantedExt.md)
- Joshua Zelinsky, "Must a Primitive Non-Deficient Number Always Have a Small Component?", Proposition (label `dichotomywithpk`).
