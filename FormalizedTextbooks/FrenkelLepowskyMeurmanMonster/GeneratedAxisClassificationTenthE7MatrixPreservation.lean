/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7ProjectorPreservation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7ConjugationActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthFlagCoordinates

/-! Every original Tenth matrix stabilizer preserves the actual enclosing E8
after genuine transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual spatial conjugate in certified physical E7 coordinates. -/
def generatedTenthE7TransportedSpatial (g : leechIsomSubgroup) : leechIsomSubgroup :=
  generatedTenthE7Isometry * g * generatedTenthE7Isometry⁻¹

private theorem original_pair_eigenspace (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g (griessConwayEncode generatedTenthAxis).1 =
      (griessConwayEncode generatedTenthAxis).1) (y : Fin 24 → ℝ) :
    generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) *ᵥ y = (2 : ℝ) • y ↔
      generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) *ᵥ g.val y =
        (2 : ℝ) • g.val y := by
  have hpair := ((generatedTenth_matrix_fix_flag_iff g).mp hg).1
  have htwo : (2 : ℝ) • generatedTenthPairProjection =
      generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) := by
    simp only [generatedTenthPairProjection, smul_smul]
    norm_num
  have hfix : conwayMatrixAction g
      (generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ)) =
        generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) := by
    rw [← htwo, map_smul, hpair]
  have hcomm (z : Fin 24 → ℝ) :
      generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) *ᵥ g.val z =
        g.val (generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) *ᵥ z) := by
    have h := conwayMatrixAction_mulVec g
      (generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ)) z
    rw [hfix] at h
    exact h
  constructor
  · intro h
    rw [hcomm, h, map_smul]
  · intro h
    apply g.val.injective
    rw [map_smul, ← hcomm, h]

/-- Every genuine original matrix fixer preserves the transported actual E7 eigenspace. -/
theorem generatedTenth_e7_matrix_fixer_eigenspace (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g (griessConwayEncode generatedTenthAxis).1 =
      (griessConwayEncode generatedTenthAxis).1) (x : Fin 24 → ℝ) :
    generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ x = (2 : ℝ) • x ↔
      generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ
          (generatedTenthE7TransportedSpatial g).val x =
        (2 : ℝ) • (generatedTenthE7TransportedSpatial g).val x := by
  let y := generatedTenthE7Isometry.val.symm x
  have hxy : generatedTenthE7Matrix *ᵥ y = x := by
    rw [← generatedTenth_e7_isometry_apply]
    exact generatedTenthE7Isometry.val.apply_symm_apply x
  have hgy : generatedTenthE7Matrix *ᵥ g.val y =
      (generatedTenthE7TransportedSpatial g).val x := by
    rw [← generatedTenth_e7_isometry_apply]
    rfl
  calc
    _ ↔ generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) *ᵥ y =
        (2 : ℝ) • y := by
      simpa only [hxy] using (generatedTenth_e7_pair_eigenspace_iff y).symm
    _ ↔ generatedTenthPairProjectionInteger.map (Int.castRingHom ℝ) *ᵥ g.val y =
        (2 : ℝ) • g.val y := original_pair_eigenspace g hg y
    _ ↔ generatedTenthE7ProjectionInteger.map (Int.castRingHom ℝ) *ᵥ
        (generatedTenthE7Matrix *ᵥ g.val y) =
          (2 : ℝ) • (generatedTenthE7Matrix *ᵥ g.val y) :=
      generatedTenth_e7_pair_eigenspace_iff (g.val y)
    _ ↔ _ := by rw [hgy]

/-- Every original actual matrix fixer preserves the entire enclosing transported E8 section. -/
theorem generatedTenth_e7_matrix_fixer_e8_section (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g (griessConwayEncode generatedTenthAxis).1 =
      (griessConwayEncode generatedTenthAxis).1) (x : Fin 24 → ℝ) :
    x ∈ generatedTenthE8CoordinateSection ↔
      (generatedTenthE7TransportedSpatial g).val x ∈ generatedTenthE8CoordinateSection :=
  generatedTenth_e8_preserved_of_e7_eigenspace (generatedTenthE7TransportedSpatial g)
    (generatedTenth_e7_matrix_fixer_eigenspace g hg) x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
