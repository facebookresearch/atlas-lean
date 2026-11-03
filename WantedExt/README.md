# WantedExt

`WantedExt` records established mathematics whose Lean implementation or proof
is intentionally deferred. It is separate from `MathlibExt` so wishlist
declarations cannot enter the proved library transitively.

Use `theorem_wanted` for propositions and `def_wanted` for missing data or
constructions. Every module using either command must directly import
`Batteries.Util.ProofWanted`. Do not use `sorry`, `sorryAx`, `admit`, custom
axioms, or `native_decide` here. Modules may import `MathlibExt` and
`CSLibExt`, but not `PhyslibExt` or any test library. Move completed results to the matching
proved library.
