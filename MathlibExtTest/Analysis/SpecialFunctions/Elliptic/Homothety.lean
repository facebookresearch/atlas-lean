/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.Homothety

@[expose] public section

open scoped Pointwise

namespace PeriodPair

example (L : PeriodPair) : IsHomothetic L L :=
  IsHomothetic.refl L

example {L L' : PeriodPair} (h : IsHomothetic L L') : IsHomothetic L' L :=
  h.symm

example {L₁ L₂ L₃ : PeriodPair} (h₁₂ : IsHomothetic L₁ L₂)
    (h₂₃ : IsHomothetic L₂ L₃) : IsHomothetic L₁ L₃ :=
  h₁₂.trans h₂₃

example : Equivalence IsHomothetic :=
  isHomothetic_equivalence

example {L L' : PeriodPair} (c : ℂ) (hc : c ≠ 0)
    (hLat : (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)) : IsHomothetic L L' :=
  ⟨c, hc, hLat⟩

/-- Consumer with the original binders. -/
theorem exactSource (L : PeriodPair) (α : ℂˣ) (z : ℂ) :
    (L.scale α).weierstrassP ((α : ℂ) * z) = ((α : ℂ) ^ 2)⁻¹ * L.weierstrassP z :=
  L.weierstrassP_scale α z

/-- Scaling by the unit `1` leaves `℘` unchanged. -/
example (L : PeriodPair) (z : ℂ) : (L.scale 1).weierstrassP z = L.weierstrassP z := by
  simpa using L.weierstrassP_scale 1 z

/-- The unit hypothesis matters: scaling both periods by `0` collapses them to
`0`, which is not `ℝ`-linearly independent, so no period pair results. -/
example (L : PeriodPair) : ¬ LinearIndependent ℝ ![(0 : ℂ) * L.ω₁, (0 : ℂ) * L.ω₂] := by
  intro h
  have h0 := h.ne_zero 0
  simp at h0

end PeriodPair
