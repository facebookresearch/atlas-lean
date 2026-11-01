/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ProjectionStabilizer

/-! Fixing the actual real projection recognizes the actual integral section stabilizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Fixing a coordinate projection implies commutation with its genuine isometry matrix. -/
theorem generatedAxisE8_projection_fixed_commute (c : Fin 24 → ZMod 2)
    (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g
      (Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1)) =
        Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1)) :
    leechIsomMatrix g * Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1) =
      Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1) * leechIsomMatrix g := by
  rw [conwayMatrixAction_eq_conjugate] at hg
  have h := congrArg (fun A => A * leechIsomMatrix g) hg
  simpa only [Matrix.mul_assoc, leechIsomMatrix_transpose_mul, Matrix.mul_one] using h

/-- Fixing a projection sends every supported integral lattice vector into the section. -/
theorem generatedAxisE8_projection_fixed_maps_support (c : Fin 24 → ZMod 2)
    (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g
      (Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1)) =
        Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1))
    (u : leechIntegral) (hu : generatedOctadSupported c u.val) :
    generatedOctadSupported c (leechIntegralAction g u).val := by
  have hc := generatedAxisE8_projection_fixed_commute c g hg
  intro i hi
  have hm (j : Fin 24) (hj : c j ≠ 0) : leechIsomMatrix g i j = 0 := by
    have h := congrArg (fun A : Matrix (Fin 24) (Fin 24) ℝ => A i j) hc
    simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul, hi, hj, ↓reduceIte,
      mul_one, zero_mul] using h
  have hz : (leechIsomMatrix g *ᵥ leechCoordinateEmbedding u.val) i = 0 := by
    change (∑ j, leechIsomMatrix g i j * ((u.val j : ℝ) / Real.sqrt 8)) = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : c j = 0
    · rw [hu j hj, Int.cast_zero, zero_div, mul_zero]
    · rw [hm j hj, zero_mul]
  rw [leechIsomMatrix_mulVec, ← leechIntegralAction_embedding] at hz
  change ((leechIntegralAction g u).val i : ℝ) / Real.sqrt 8 = 0 at hz
  have hn : Real.sqrt 8 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hiReal := (div_eq_iff hn).mp hz
  norm_num only [zero_mul] at hiReal
  exact_mod_cast hiReal

/-- Fixing the actual projection preserves the actual integral section in both directions. -/
theorem generatedAxisE8_preserves_of_matrix_action (c : Fin 24 → ZMod 2)
    (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g
      (Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1)) =
        Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1)) :
    generatedOctadPreserves c g := by
  let P := Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1)
  have hInv : conwayMatrixAction g⁻¹ P = P := by
    rw [map_inv]
    change (conwayMatrixAction g).symm P = P
    calc
      (conwayMatrixAction g).symm P =
          (conwayMatrixAction g).symm ((conwayMatrixAction g) P) := by rw [hg]
      _ = P := (conwayMatrixAction g).symm_apply_apply P
  intro u
  constructor
  · intro hu
    have h := generatedAxisE8_projection_fixed_maps_support c g⁻¹ hInv
      (leechIntegralAction g u) hu
    rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h
    exact h
  · exact generatedAxisE8_projection_fixed_maps_support c g hg u

/-- The real projection stabilizer is exactly the actual integral section stabilizer. -/
theorem generatedAxisE8_matrix_action_iff_section_stabilizer (c : Fin 24 → ZMod 2)
    (g : leechIsomSubgroup) :
    conwayMatrixAction g (Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1)) =
        Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1) ↔
      generatedAxisE8ImageSection g c = generatedAxisE8CoordinateSection c :=
  ⟨fun h => generatedAxisE8_preserving_image c g
    (generatedAxisE8_preserves_of_matrix_action c g h),
    generatedAxisE8_section_stabilizer_matrix_action c g⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
