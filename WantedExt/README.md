# WantedExt

`WantedExt` records established mathematics whose Lean implementation or proof
is intentionally deferred. It is separate from the proved libraries so wishlist
declarations cannot enter them transitively.

Use `theorem_wanted` for propositions and `def_wanted` for missing data or
constructions. Every module using either command must directly import
`Batteries.Util.ProofWanted`. Do not use `sorry`, `sorryAx`, `admit`, custom
axioms, or `native_decide` here. Modules may import `MathlibExt`, `CSLibExt`,
`PhyslibExt`, and `Domains`, but not any test library. Reuse the proved models'
definitions rather than duplicating them here. No proved library or test
library may import `WantedExt`. Move completed results to the matching proved
library.
