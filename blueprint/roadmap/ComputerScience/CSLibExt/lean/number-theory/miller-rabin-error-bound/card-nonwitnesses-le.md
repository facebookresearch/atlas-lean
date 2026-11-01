---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.card_nonwitnesses_le
---

# Card nonwitnesses le

CLRS Theorem 31.38: an odd composite `n` has at most `(n - 1) / 2` non-witnesses among the
bases `1, …, n - 1`, that is, at least `(n - 1) / 2` witnesses.

## Depends on

- [Nonwitnesses](nonwitnesses.md)

## Proof depends on

- [Card nonwitnesses le of carmichael](card-nonwitnesses-le-of-carmichael.md)
- [Card nonwitnesses le of pow ne one](card-nonwitnesses-le-of-pow-ne-one.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound](../../../../../../sources/v2/CSLibExt.md)
