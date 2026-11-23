# Generator neg one sub

Conjugation of the backward generator by allele relabeling: for an
arbitrary test function `f` and every `y`,
`generator (-σ) f (1 - y) = generator σ (fun z => f (1 - z)) y`. The neutral
part is invariant under `y ↦ 1 - y` while the genic drift changes sign. No
regularity is needed because the derivative is the totalized Mathlib
derivative; the martingale-problem transport below applies the identity to
its smooth test functions.
