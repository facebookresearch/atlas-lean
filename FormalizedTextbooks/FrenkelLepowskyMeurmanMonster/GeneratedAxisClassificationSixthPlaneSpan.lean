/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPlaneSpanData

/-! The projection range is exactly the real span of two genuine shortest Leech roots. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The second root is the actual preferred minus pair on coordinates sixteen and nineteen. -/
def generatedSixthPlaneSecondShort : GriessShortIndex := Sum.inl (0, generatedSixthTargetPair 1)

/-- The second integer root is also the original preferred physical catalogue vector. -/
theorem generatedSixth_plane_second_root_actual :
    griessShortIntegral generatedSixthPlaneSecondShort = generatedSixthPlaneSecondRoot := by
  ext i
  simp only [generatedSixthPlaneSecondShort, griessShortIntegral,
    (generatedSixth_pair_coordinate_certificate 1).2, Matrix.cons_val_one, Matrix.cons_val_zero,
    ite_true, generatedSixthPlaneSecondRoot]
  ring

/-- Both actual shortest roots factor the real orthogonal projection. -/
theorem generatedSixth_plane_projection_factor :
    generatedSixthPlaneProjection =
      (Real.sqrt 8 / 12) •
        Matrix.vecMulVec (griessShortVector generatedSixthPlaneShort)
          (fun i => (generatedSixthPlaneFirstRow i : ℝ)) +
      (Real.sqrt 8 / 12) •
        Matrix.vecMulVec (griessShortVector generatedSixthPlaneSecondShort)
          (fun i => (generatedSixthPlaneSecondRow i : ℝ)) := by
  ext i j
  have h := congrFun (congrFun generatedSixth_plane_numerator_factor i) j
  change 4 * generatedSixthPlaneNumerator i j =
    generatedSixthPlaneRoot i * generatedSixthPlaneFirstRow j +
      generatedSixthPlaneSecondRoot i * generatedSixthPlaneSecondRow j at h
  have hr : 4 * (generatedSixthPlaneNumerator i j : ℝ) =
      (generatedSixthPlaneRoot i : ℝ) * (generatedSixthPlaneFirstRow j : ℝ) +
      (generatedSixthPlaneSecondRoot i : ℝ) * (generatedSixthPlaneSecondRow j : ℝ) := by
    exact_mod_cast h
  have hs : Real.sqrt 8 ≠ 0 := by positivity
  simp only [generatedSixthPlaneProjection, Matrix.map_apply, Int.coe_castRingHom,
    Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    griessShortVector, generatedSixth_plane_root_actual, generatedSixth_plane_second_root_actual]
  field_simp [hs]
  nlinarith only [hr]

/-- The actual second shortest root is fixed by the same orthogonal projection. -/
theorem generatedSixth_plane_projection_second_root :
    generatedSixthPlaneProjection *ᵥ griessShortVector generatedSixthPlaneSecondShort =
      griessShortVector generatedSixthPlaneSecondShort := by
  ext i
  have h := congrFun generatedSixth_plane_numerator_second_root i
  change (∑ j, generatedSixthPlaneNumerator i j * generatedSixthPlaneSecondRoot j) =
    3 * generatedSixthPlaneSecondRoot i at h
  have hr : (∑ j, (generatedSixthPlaneNumerator i j : ℝ) *
      (generatedSixthPlaneSecondRoot j : ℝ)) = 3 * (generatedSixthPlaneSecondRoot i : ℝ) := by
    exact_mod_cast h
  simp only [Matrix.mulVec, dotProduct, generatedSixthPlaneProjection, Matrix.smul_apply,
    Matrix.map_apply, Int.coe_castRingHom, smul_eq_mul, griessShortVector,
    generatedSixth_plane_second_root_actual]
  calc
    _ = (∑ j, (generatedSixthPlaneNumerator i j : ℝ) *
      (generatedSixthPlaneSecondRoot j : ℝ)) / (3 * Real.sqrt 8) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (generatedSixthPlaneSecondRoot i : ℝ) / Real.sqrt 8 := by rw [hr]; ring

/-- The genuine rooted-A2 plane is the real span of these two actual Leech short vectors. -/
def generatedSixthRootedPlane : Submodule ℝ (Fin 24 → ℝ) :=
  Submodule.span ℝ {griessShortVector generatedSixthPlaneShort,
    griessShortVector generatedSixthPlaneSecondShort}

/-- The actual matrix projection range equals the genuine two-root plane. -/
theorem generatedSixth_plane_projection_range :
    LinearMap.range (Matrix.toLin' generatedSixthPlaneProjection) = generatedSixthRootedPlane := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    change generatedSixthPlaneProjection *ᵥ v ∈ generatedSixthRootedPlane
    rw [generatedSixth_plane_projection_factor, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      Matrix.vecMulVec_mulVec]
    simp only [op_smul_eq_smul]
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact Set.mem_insert _ _
    · apply Submodule.smul_mem
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      exact ⟨griessShortVector generatedSixthPlaneShort, generatedSixth_plane_projection_root⟩
    · have hx := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨griessShortVector generatedSixthPlaneSecondShort,
        generatedSixth_plane_projection_second_root⟩

/-- The two genuine lattice roots have square sums32 and actual integer pairing16. -/
theorem generatedSixth_plane_lattice_roots :
    leechSquareSum (griessShortLatticeVector generatedSixthPlaneShort).val = 32 ∧
      leechSquareSum (griessShortLatticeVector generatedSixthPlaneSecondShort).val = 32 ∧
      leechIntegralPairing (griessShortLatticeVector generatedSixthPlaneShort).val
        (griessShortLatticeVector generatedSixthPlaneSecondShort).val = 16 := by
  refine ⟨griessShortIntegral_squareSum generatedSixthPlaneShort,
    griessShortIntegral_squareSum generatedSixthPlaneSecondShort, ?_⟩
  change (∑ i, griessShortIntegral generatedSixthPlaneShort i *
    griessShortIntegral generatedSixthPlaneSecondShort i) = 16
  rw [generatedSixth_plane_root_actual, generatedSixth_plane_second_root_actual]
  exact generatedSixth_plane_roots_norm_pairing.2.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
