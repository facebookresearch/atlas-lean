# Mset To Set

`set_mset s`: the set underlying a multiset (Isabelle `set_mset`).
Mathlib has no `Multiset.toSet` in this toolchain (checked with
Loogle: only `Multiset.toFinset`, which needs `DecidableEq`), so it is
defined here as `{x | x ∈ s}`.
