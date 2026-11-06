/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual source-word orbit certificates put every independent norm-two reflection in the image. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3ReflectionConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3NormTwoOrbitProofs

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal norm-two orbit begins at the exact first original Cartan root. -/
theorem y322Orthogonal3NormTwoPoint_source_root :
    y322Orthogonal3NormTwoPoint = y322Orthogonal3Root 0 := by
  decide +kernel

/-- Complete source-vector recurrences and coverage give every genuine norm-two reflection. -/
theorem y322Orthogonal3NormTwoReflection_mem_image_of_checked
    (checked : ∀ i : Fin 702, y322Orthogonal3NormTwoCheckAt i.val)
    (coverChecked : ∀ c : Fin 2187, y322Orthogonal3NormTwoCoverCheckAt c.val)
    (v : Fin 7 → ZMod 3) (hv : y322Orthogonal3VectorNorm v = 2)
    (hv0 : y322Orthogonal3VectorNorm v ≠ 0) :
    y322Orthogonal3RootReflection v hv0 ∈ y322Orthogonal3Image := by
  obtain ⟨g, hg, hact⟩ :=
    y322Orthogonal3NormTwo_image_transitive_of_checked checked coverChecked v hv
  have hp : y322Orthogonal3VectorNorm y322Orthogonal3NormTwoPoint ≠ 0 := by
    rw [y322Orthogonal3NormTwoPoint_source_root]
    exact y322Orthogonal3Root_nonisotropic 0
  have hgp : y322Orthogonal3VectorNorm (g.val *ᵥ y322Orthogonal3NormTwoPoint) ≠ 0 := by
    rw [hact]
    exact hv0
  have href : y322Orthogonal3RootReflection y322Orthogonal3NormTwoPoint hp ∈
      y322Orthogonal3Image := by
    have hePoint := y322Orthogonal3RootReflection_congr y322Orthogonal3NormTwoPoint
      (y322Orthogonal3Root 0) hp (y322Orthogonal3Root_nonisotropic 0)
      y322Orthogonal3NormTwoPoint_source_root
    rw [hePoint, y322Orthogonal3RootReflection_generator]
    exact ⟨PresentedGroup.of 0, y322Orthogonal3Hom_generator 0⟩
  have he := y322Orthogonal3RootReflection_conjugate g (y322Orthogonal3Image_le_full hg)
    y322Orthogonal3NormTwoPoint hp hgp
  have h := y322Orthogonal3Image.mul_mem (y322Orthogonal3Image.mul_mem hg href)
    (y322Orthogonal3Image.inv_mem hg)
  rw [← he] at h
  rw [y322Orthogonal3RootReflection_congr _ v hgp hv0 hact] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
