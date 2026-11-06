/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual original F12 source word gives the reflection in the independent fixed-vector line. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3NormTwoReflectionFormula

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The independent fixed vector has its actual norm-two value. -/
theorem y422Orthogonal3FixedVector_norm_two :
    y422Orthogonal3VectorNorm y422Orthogonal3FixedVector = 2 :=
  y422Orthogonal3FixedVector_norm

/-- The independent fixed-line reflection is an actual invertible finite-form reflection. -/
def y422Orthogonal3FixedReflection : Matrix.GeneralLinearGroup (Fin 8) (ZMod 3) :=
  y422Orthogonal3RootReflection y422Orthogonal3FixedVector
    (by rw [y422Orthogonal3FixedVector_norm_two]; decide)

/-- The original source quotient map retains its literal projective free-word lift. -/
theorem y422Orthogonal3ProjectiveHom_quotient :
    y422Orthogonal3ProjectiveHom.comp (PresentedGroup.mk y422Relations) =
      FreeGroup.lift y422Orthogonal3ProjectiveGenerator := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
  exact y422Orthogonal3ProjectiveHom_generator i

/-- The actual longest source-word matrix is its checked ninth source-prefix power. -/
theorem y422Orthogonal3Longest_cached :
    y422Orthogonal3Longest = y422Orthogonal3LongestPowers 9 := by
  unfold y422Orthogonal3Longest
  rw [← y422Orthogonal3Longest_prefix_value]
  exact y422Orthogonal3Longest_power_value 9

set_option maxRecDepth 100000 in
-- This exact eight-dimensional source-word matrix is compared with the independent reflection.
/-- The actual cached F12 matrix is minus the reflection in the independent fixed-vector line. -/
theorem y422Orthogonal3Longest_fixedReflection_matrix :
    y422Orthogonal3LongestPowers 9 =
      (Matrix.GeneralLinearGroup.scalar (Fin 8) (-1 : (ZMod 3)ˣ) *
        y422Orthogonal3FixedReflection).val := by
  rw [Units.val_mul]
  unfold y422Orthogonal3FixedReflection
  rw [y422Orthogonal3RootReflection_norm_two_matrix
    y422Orthogonal3FixedVector y422Orthogonal3FixedVector_norm_two]
  decide +kernel

/-- The original F12 lifts to a scalar times its genuine fixed-line reflection. -/
theorem y422Orthogonal3F12_fixedReflection :
    FreeGroup.lift y422Orthogonal3Generator y422F12 =
      Matrix.GeneralLinearGroup.scalar (Fin 8) (-1 : (ZMod 3)ˣ) *
        y422Orthogonal3FixedReflection := by
  apply Units.ext
  rw [y422Orthogonal3Longest_matrix, y422Orthogonal3Longest_cached]
  exact y422Orthogonal3Longest_fixedReflection_matrix

/-- Original F12 gives the independent fixed-line projective reflection. -/
theorem y422Orthogonal3ProjectiveHom_F12 :
    y422Orthogonal3ProjectiveHom (PresentedGroup.mk y422Relations y422F12) =
      Matrix.ProjGenLinGroup.mk y422Orthogonal3FixedReflection := by
  change (y422Orthogonal3ProjectiveHom.comp (PresentedGroup.mk y422Relations)) y422F12 = _
  rw [y422Orthogonal3ProjectiveHom_quotient, y422Orthogonal3ProjectiveLift,
    MonoidHom.comp_apply, y422Orthogonal3F12_fixedReflection, map_mul,
    Matrix.ProjGenLinGroup.mk_scalar, one_mul]

/-- The independent fixed-line reflection belongs to the actual original source image. -/
theorem y422Orthogonal3FixedReflection_projective_mem_image :
    Matrix.ProjGenLinGroup.mk y422Orthogonal3FixedReflection ∈
      y422Orthogonal3ProjectiveImage :=
  ⟨PresentedGroup.mk y422Relations y422F12, y422Orthogonal3ProjectiveHom_F12⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
