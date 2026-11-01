/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact semantic consequences of original-source norm orbit and coverage certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3NormTwoOrbitCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3NormTwoCoverData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- A bounded finite check verifies the literal source-word recurrence and exact vector norm. -/
theorem y322Orthogonal3NormTwoCheck_unpack (i : Fin 702) (h : y322Orthogonal3NormTwoCheckAt i.val) :
    y322InverseWordOrbitChecked y322Orthogonal3NormTwoWord
      y322Orthogonal3NormTwoParent y322Orthogonal3NormTwoGenerator
      y322Orthogonal3NormTwoPoint y322Orthogonal3NormTwoVector i ∧
      y322Orthogonal3VectorNorm (y322Orthogonal3NormTwoVector i) = 2 := by
  simpa only [y322Orthogonal3NormTwoCheckAt, dite_eq_left i.isLt] using h

/-- Verified literal recurrences give the exact actual inverse source-word matrix action. -/
theorem y322Orthogonal3NormTwo_source_of_checked
    (checked : ∀ i : Fin 702, y322Orthogonal3NormTwoCheckAt i.val) (i : Fin 702) :
    (y322Orthogonal3Hom (y322PositiveWord (y322Orthogonal3NormTwoWord i)))⁻¹.val *ᵥ
      y322Orthogonal3NormTwoPoint = y322Orthogonal3NormTwoVector i :=
  y322InverseWordOrbit_checked_image _ _ _ _ _
    (fun j => (y322Orthogonal3NormTwoCheck_unpack j (checked j)).1) i

/-- Exact bounded coordinate coverage gives an actual source-orbit column for every norm vector. -/
theorem y322Orthogonal3NormTwo_cover_of_checked
    (checked : ∀ c : Fin 2187, y322Orthogonal3NormTwoCoverCheckAt c.val)
    (v : Fin 7 → ZMod 3) (hv : y322Orthogonal3VectorNorm v = 2) :
    ∃ i : Fin 702, y322Orthogonal3NormTwoVector i = v := by
  let c : Fin 2187 := ⟨y322Orthogonal3VectorCode v, y322Orthogonal3VectorCode_lt v⟩
  have hd : y322Orthogonal3VectorDecode c = v := y322Orthogonal3VectorDecode_encode v
  have hn : y322Orthogonal3VectorNorm (y322Orthogonal3VectorDecode c) = 2 := by
    rw [hd]
    exact hv
  have h := checked c
  simp only [y322Orthogonal3NormTwoCoverCheckAt, dite_eq_left c.isLt, ite_eq_left hn] at h
  exact ⟨y322Orthogonal3NormTwoCoverLabel c, h.trans hd⟩

/-- Every vector of the independent norm level is reached by an actual original source image. -/
theorem y322Orthogonal3NormTwo_image_transitive_of_checked
    (checked : ∀ i : Fin 702, y322Orthogonal3NormTwoCheckAt i.val)
    (coverChecked : ∀ c : Fin 2187, y322Orthogonal3NormTwoCoverCheckAt c.val)
    (v : Fin 7 → ZMod 3) (hv : y322Orthogonal3VectorNorm v = 2) :
    ∃ g ∈ y322Orthogonal3Image, g.val *ᵥ y322Orthogonal3NormTwoPoint = v := by
  obtain ⟨i, hi⟩ := y322Orthogonal3NormTwo_cover_of_checked coverChecked v hv
  refine ⟨(y322Orthogonal3Hom (y322PositiveWord (y322Orthogonal3NormTwoWord i)))⁻¹, ?_, ?_⟩
  · exact y322Orthogonal3Image.inv_mem ⟨_, rfl⟩
  · exact (y322Orthogonal3NormTwo_source_of_checked checked i).trans hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
