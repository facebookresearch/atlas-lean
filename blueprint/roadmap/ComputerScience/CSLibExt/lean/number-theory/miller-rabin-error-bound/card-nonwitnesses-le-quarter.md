---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.card_nonwitnesses_le_quarter
---

# The `1/4` bound

**The `1/4` bound.** An odd composite `n` has at most `(n - 1) / 4` non-witnesses among the
bases `1, …, n - 1`, so one uniformly random base fails to expose `n` with probability at most
`1/4`.

## Depends on

- [Nonwitnesses](nonwitnesses.md)

## Proof depends on

- [Card nonwitnesses le quarter of carmichael](card-nonwitnesses-le-quarter-of-carmicha.md)
- [Card nonwitnesses le quarter of pow ne one](card-nonwitnesses-le-quarter-of-pow-ne-o.md)
- [Card nonwitnesses le quarter of prime pow](card-nonwitnesses-le-quarter-of-prime-po.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound](../../../../../../sources/v2/CSLibExt.md)
