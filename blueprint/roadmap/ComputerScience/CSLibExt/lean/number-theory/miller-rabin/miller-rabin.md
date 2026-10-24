---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.millerRabin
---

# Miller Rabin

CLRS `MILLER-RABIN(n, s)` with the bases given explicitly: `false` (*composite*) as soon as a
base is a witness, `true` (*prime*) otherwise. The caller supplies bases in `1, …, n - 1`, as
CLRS's `RANDOM(1, n - 1)` does; only then is a *composite* answer guaranteed correct
(`not_prime_of_millerRabin_eq_false`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Witness](witness.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabin](../../../../../../sources/v2/CSLibExt.md)
