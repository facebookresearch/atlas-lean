/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitEdgesActions

/-! The actual original matrix stabilizer and its genuine standard-coordinate root action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All genuine Leech isometries preserving the complete original Tenth matrix. -/
def generatedTenthE7OriginalMatrixGroup : Subgroup leechIsomSubgroup where
  carrier := {g | conwayMatrixAction g (griessConwayEncode generatedTenthAxis).1 =
    (griessConwayEncode generatedTenthAxis).1}
  one_mem' := by
    change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl
  mul_mem' := by
    intro g h hg hh
    change conwayMatrixAction (g * h) _ = _
    rw [map_mul]
    change conwayMatrixAction g (conwayMatrixAction h _) = _
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    change conwayMatrixAction g⁻¹ _ = _
    rw [map_inv]
    change (conwayMatrixAction g).symm _ = _
    calc
      _ = (conwayMatrixAction g).symm
          (conwayMatrixAction g (griessConwayEncode generatedTenthAxis).1) := by rw [hg]
      _ = _ := LinearEquiv.symm_apply_apply _ _

/-- The actual complete coordinate transport from standard roots to original matrix coordinates. -/
def generatedTenthE7OrbitTransport : leechIsomSubgroup :=
  generatedTenthE7Isometry⁻¹ * golayPermutationIsometry generatedTenthE8StandardPermutation

/-- Conjugation by that genuine isometry, as an actual group homomorphism. -/
def generatedTenthE7OrbitConjugation : leechIsomSubgroup →* leechIsomSubgroup where
  toFun g := generatedTenthE7OrbitTransport * g * generatedTenthE7OrbitTransport⁻¹
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

/-- The entire original matrix group pulled back into standard root coordinates. -/
def generatedTenthE7StandardMatrixGroup : Subgroup leechIsomSubgroup :=
  generatedTenthE7OriginalMatrixGroup.comap generatedTenthE7OrbitConjugation

/-- Both root-orbit letters belong to the entire actual original matrix stabilizer
after transport. -/
theorem generatedTenth_e7_orbit_letter_mem (k : Fin 2) :
    generatedTenthE7OrbitSpatialLetter k ∈ generatedTenthE7StandardMatrixGroup := by
  change conwayMatrixAction
    (generatedTenthE7OrbitConjugation (generatedTenthE7OrbitSpatialLetter k))
      (griessConwayEncode generatedTenthAxis).1 = _
  by_cases hk : k = 0
  · have he : generatedTenthE7OrbitConjugation (generatedTenthE7OrbitSpatialLetter k) =
        generatedTenthE7XiOriginal := by
      simp [generatedTenthE7OrbitConjugation, generatedTenthE7OrbitSpatialLetter, hk,
        generatedTenthE7OrbitTransport, generatedTenthE7XiOriginal,
        generatedTenthE7XiActual, mul_assoc]
    rw [he]
    exact generatedTenth_e7_xi_original_matrix_fix
  · have he : generatedTenthE7OrbitConjugation (generatedTenthE7OrbitSpatialLetter k) =
        generatedTenthE7OrbitMonoOriginal := by
      simp [generatedTenthE7OrbitConjugation, generatedTenthE7OrbitSpatialLetter, hk,
        generatedTenthE7OrbitTransport, generatedTenthE7OrbitMonoOriginal,
        generatedTenthE7OrbitMonoActual, mul_assoc]
    rw [he]
    exact generatedTenth_e7_orbit_mono_original_matrix_fix

/-- Either genuine correcting root-orbit letter as an element of the whole actual subgroup. -/
def generatedTenthE7RootOrbitLetter (k : Fin 2) : generatedTenthE7StandardMatrixGroup :=
  ⟨generatedTenthE7OrbitSpatialLetter k, generatedTenth_e7_orbit_letter_mem k⟩

/-- Actual original matrix fixers that also fix the normal root positively. -/
def generatedTenthE7PositiveRootMatrixGroup : Subgroup generatedTenthE7StandardMatrixGroup where
  carrier := {g | leechIntegralAction g.val generatedTenthE7OrbitNormalRoot =
    generatedTenthE7OrbitNormalRoot}
  one_mem' := by
    change leechIntegralAction 1 _ = _
    rw [map_one]
    rfl
  mul_mem' := by
    intro g h hg hh
    change leechIntegralAction (g.val * h.val) _ = _
    rw [map_mul]
    change leechIntegralAction g.val (leechIntegralAction h.val _) = _
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    change leechIntegralAction g.val⁻¹ _ = _
    rw [map_inv]
    change (leechIntegralAction g.val).symm _ = _
    calc
      _ = (leechIntegralAction g.val).symm
          (leechIntegralAction g.val generatedTenthE7OrbitNormalRoot) := by rw [hg]
      _ = _ := LinearEquiv.symm_apply_apply _ _

/-- Both genuine correcting letters as positively normal-fixing actual matrix fixers. -/
def generatedTenthE7RootOrbitPositiveLetter (k : Fin 2) : generatedTenthE7PositiveRootMatrixGroup :=
  ⟨generatedTenthE7RootOrbitLetter k, generatedTenth_e7_orbit_letter_normal k⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
