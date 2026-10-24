---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.card_millerRabin_errors_le_quarter
---

# Card miller Rabin errors le quarter

The `1/4` bound in counting form for `s` independent bases: at most `((n - 1) / 4)^s` of the
`(n - 1)^s` lists make `MILLER-RABIN` answer *prime* on an odd composite `n`, so the error
probability is at most `4^(-s)`.

## Depends on

- [Miller Rabin](../miller-rabin/miller-rabin.md)

## Proof depends on

- [The `1/4` bound](card-nonwitnesses-le-quarter.md)
- [Miller Rabin eq true iff](miller-rabin-eq-true-iff.md)
- [Nonwitnesses](nonwitnesses.md)
- [Witness](../miller-rabin/witness.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound](../../../../../../sources/v2/CSLibExt.md)
