/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The original source image is the independently specified group of all norm-two reflections. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3NormTwoOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3ReflectionConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3NormTwoGroup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every actual inverse source-path projective matrix belongs to the original source image. -/
theorem y422Orthogonal3TPathValue_inverse_projective_mem (i : Fin 9033) :
    Matrix.ProjGenLinGroup.mk (y422Orthogonal3TPathValue i)⁻¹ ∈
      y422Orthogonal3ProjectiveImage := by
  refine ⟨(y422TPathValue i)⁻¹, ?_⟩
  simp only [map_inv, y422Orthogonal3TPathValue_projective]

/-- Every actual source-orbit root reflection belongs to the original source projective image. -/
theorem y422Orthogonal3TPathVector_reflection_projective_mem (i : Fin 9033) :
    Matrix.ProjGenLinGroup.mk
      (y422Orthogonal3RootReflection (y422Orthogonal3TPathVector i)
        (by rw [y422Orthogonal3TPathVector_norm_two]; decide)) ∈
      y422Orthogonal3ProjectiveImage := by
  let A := y422Orthogonal3TPathValue i
  have hp := y422Orthogonal3TPathValue_inverse_projective_mem i
  have hf := y422Orthogonal3FixedReflection_projective_mem_image
  have hc := y422Orthogonal3ProjectiveImage.mul_mem
    (y422Orthogonal3ProjectiveImage.mul_mem hp hf)
    (y422Orthogonal3ProjectiveImage.inv_mem hp)
  have hg : A⁻¹ ∈ y422Orthogonal3FullGroup :=
    y422Orthogonal3FullGroup.inv_mem (y422Orthogonal3TPathValue_mem_full i)
  have he : y422Orthogonal3RootReflection (y422Orthogonal3TPathVector i)
      (by rw [y422Orthogonal3TPathVector_norm_two]; decide) =
      A⁻¹ * y422Orthogonal3FixedReflection * A := by
    have h := y422Orthogonal3RootReflection_conjugate A⁻¹ hg
      y422Orthogonal3FixedVector
      (by rw [y422Orthogonal3FixedVector_norm_two]; decide)
      (by change y422Orthogonal3VectorNorm (y422Orthogonal3TPathVector i) ≠ 0
          rw [y422Orthogonal3TPathVector_norm_two]; decide)
    simpa only [inv_inv, y422Orthogonal3FixedReflection,
      y422Orthogonal3TPathVector, A] using h
  rw [he]
  simpa only [map_mul, map_inv, inv_inv, A] using hc

/-- Every independent norm-two root reflection belongs to the actual original source image. -/
theorem y422Orthogonal3NormTwoReflection_projective_mem (v : Fin 8 → ZMod 3)
    (hv : y422Orthogonal3VectorNorm v = 2) :
    Matrix.ProjGenLinGroup.mk (y422Orthogonal3RootReflection v (by rw [hv]; decide)) ∈
      y422Orthogonal3ProjectiveImage := by
  obtain ⟨i, h | h⟩ := y422Orthogonal3NormTwo_source_cover v hv
  · subst v
    exact y422Orthogonal3TPathVector_reflection_projective_mem _
  · subst v
    rw [y422Orthogonal3RootReflection_norm_two_neg _
      (y422Orthogonal3TPathVector_norm_two _)]
    exact y422Orthogonal3TPathVector_reflection_projective_mem _

/-- The entire independently specified norm-two reflection group lies in the actual source image. -/
theorem y422Orthogonal3NormTwoProjectiveGroup_le_image :
    y422Orthogonal3NormTwoProjectiveGroup ≤ y422Orthogonal3ProjectiveImage := by
  apply (Subgroup.closure_le y422Orthogonal3ProjectiveImage).mpr
  rintro g ⟨v, rfl⟩
  exact y422Orthogonal3NormTwoReflection_projective_mem v.val v.property

/-- Original source generators and complete actual orbit coverage identify the independent group. -/
theorem y422Orthogonal3ProjectiveImage_eq_normTwoProjectiveGroup :
    y422Orthogonal3ProjectiveImage = y422Orthogonal3NormTwoProjectiveGroup :=
  le_antisymm y422Orthogonal3ProjectiveImage_le_normTwoProjectiveGroup
    y422Orthogonal3NormTwoProjectiveGroup_le_image

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
