/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22FiniteData

/-! Ordinary kernel certificates for the literal spanning trees. The geometric binding
of their edges is supplied separately through the actual Golay hexad catalogue. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The global tree lists every one of the 231 pair addresses exactly once. -/
theorem co1ResidueM22GlobalOrder_bijective : Function.Bijective co1ResidueM22GlobalOrder := by
  decide +kernel

/-- The global tree starts at the distinguished pair address. -/
theorem co1ResidueM22GlobalOrder_zero : co1ResidueM22GlobalOrder 0 = 0 := by
  decide +kernel

/-- Every nonroot global node has an earlier parent connected by a cached distant edge. -/
theorem co1ResidueM22GlobalParent_edges : ∀ k : Fin 231, k.val ≠ 0 →
    (co1ResidueM22GlobalParent k).val < k.val ∧
      co1ResidueM22FiniteDistant
        (co1ResidueM22GlobalOrder (co1ResidueM22GlobalParent k))
        (co1ResidueM22GlobalOrder k) = true := by
  decide +kernel

/-- The local tree lists exactly the distant neighbors of the distinguished point. -/
theorem co1ResidueM22LocalOrder_covers : ∀ i : Fin 231,
    co1ResidueM22FiniteDistant 0 i = true ↔
      ∃ k : Fin 160, co1ResidueM22LocalOrder k = i := by
  decide +kernel

/-- Each nonroot local edge uses a cached hexad matching and a third point nearby the base. -/
theorem co1ResidueM22LocalParent_edges : ∀ k : Fin 160, k.val ≠ 0 →
    (co1ResidueM22LocalParent k).val < k.val ∧
      (co1ResidueM22FinitePointMasks
          (co1ResidueM22LocalOrder (co1ResidueM22LocalParent k)) |||
        co1ResidueM22FinitePointMasks (co1ResidueM22LocalOrder k) |||
        co1ResidueM22FinitePointMasks (co1ResidueM22LocalThird k)) =
          co1ResidueM22FiniteHexadMasks (co1ResidueM22LocalHexad k) ∧
      co1ResidueM22FiniteDistant 0 (co1ResidueM22LocalThird k) = false := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
