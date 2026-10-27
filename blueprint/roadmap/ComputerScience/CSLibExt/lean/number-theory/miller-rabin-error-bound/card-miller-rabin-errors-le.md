---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.card_millerRabin_errors_le
---

# Card miller Rabin errors le

CLRS Theorem 31.39 in counting form: of the `(n - 1)^s` lists of `s` bases from
`1, …, n - 1`, at most `((n - 1) / 2)^s` make `MILLER-RABIN` answer *prime* on an odd composite
`n`, so with uniformly random bases the error probability is at most `2^(-s)`.

## Depends on

- [Miller Rabin](../miller-rabin/miller-rabin.md)

## Proof depends on

- [Card nonwitnesses le](card-nonwitnesses-le.md)
- [Miller Rabin eq true iff](miller-rabin-eq-true-iff.md)
- [Nonwitnesses](nonwitnesses.md)
- [Witness](../miller-rabin/witness.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound](../../../../../../sources/v2/CSLibExt.md)
