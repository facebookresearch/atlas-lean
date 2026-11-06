/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationE8Rooted
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

/-! Integral section preservation fixes the genuine real coordinate projection. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A section-preserving actual isometry has no matrix entry leaving its coordinate section. -/
theorem generatedAxisE8_preserving_matrix_zero (c : Fin 24 → ZMod 2)
    (g : leechIsomSubgroup) (hg : generatedOctadPreserves c g) (i j : Fin 24)
    (hi : c i = 0) (hj : c j ≠ 0) : leechIsomMatrix g i j = 0 := by
  have hs := (hg (leechCoordinateFrameLattice j)).mpr
    (generatedAxisE8_frame_supported c j hj)
  have hz := hs i hi
  have hf : leechCoordinateEmbedding (leechCoordinateFrameLattice j).val =
      (8 / Real.sqrt 8 : ℝ) • (Pi.single j 1 : Fin 24 → ℝ) := by
    ext k
    by_cases hkj : k = j <;>
      simp [leechCoordinateEmbedding, leechCoordinateFrameLattice,
        leechCoordinateFrameVector, hkj]
  have he := leechIntegralAction_embedding g (leechCoordinateFrameLattice j)
  rw [hf, map_smul] at he
  have hk := congrFun he i
  change ((leechIntegralAction g (leechCoordinateFrameLattice j)).val i : ℝ) /
    Real.sqrt 8 = (8 / Real.sqrt 8) * leechIsomMatrix g i j at hk
  rw [hz, Int.cast_zero, zero_div] at hk
  have hn : (8 / Real.sqrt 8 : ℝ) ≠ 0 :=
    div_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  exact (mul_eq_zero.mp hk.symm).resolve_left hn

/-- The genuine coordinate matrix commutes with the coordinate section projection. -/
theorem generatedAxisE8_preserving_projection_commute (c : Fin 24 → ZMod 2)
    (g : leechIsomSubgroup) (hg : generatedOctadPreserves c g) :
    leechIsomMatrix g * Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1) =
      Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1) * leechIsomMatrix g := by
  have hrev (i j : Fin 24) (hi : c i ≠ 0) (hj : c j = 0) :
      leechIsomMatrix g i j = 0 := by
    have h := generatedAxisE8_preserving_matrix_zero c g⁻¹
      (generatedAxisE8_preserves_inv c g hg) j i hj hi
    change g.val.symm (Pi.single i 1) j = 0 at h
    rw [leechIsom_inverse_coordinate] at h
    exact h
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : c i = 0 <;> by_cases hj : c j = 0
  · simp [hi, hj]
  · simp [hi, hj, generatedAxisE8_preserving_matrix_zero c g hg i j hi hj]
  · simp [hi, hj, hrev i j hi hj]
  · simp [hi, hj]

/-- Preserving the actual integral section fixes its projection in the actual matrix action. -/
theorem generatedAxisE8_preserving_matrix_action (c : Fin 24 → ZMod 2)
    (g : leechIsomSubgroup) (hg : generatedOctadPreserves c g) :
    conwayMatrixAction g (Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1)) =
      Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1) := by
  rw [conwayMatrixAction_eq_conjugate, generatedAxisE8_preserving_projection_commute c g hg,
    Matrix.mul_assoc, mul_eq_one_comm.mp (leechIsomMatrix_transpose_mul g), Matrix.mul_one]

/-- Stabilizing the genuine integral submodule is equivalent to preserving literal support. -/
theorem generatedAxisE8_preserves_of_image_eq (c : Fin 24 → ZMod 2)
    (g : leechIsomSubgroup)
    (hg : generatedAxisE8ImageSection g c = generatedAxisE8CoordinateSection c) :
    generatedOctadPreserves c g := by
  intro u
  constructor
  · intro hu
    have hm : leechIntegralAction g u ∈ generatedAxisE8ImageSection g c := by
      rw [hg]
      exact hu
    obtain ⟨v, hv, he⟩ := (generatedAxisE8ImageSection_mem g c _).mp hm
    have hvu : v = u := (leechIntegralAction g).injective he
    exact hvu ▸ hv
  · intro hu
    have hm := (generatedAxisE8ImageSection_mem g c (leechIntegralAction g u)).mpr
      ⟨u, hu, rfl⟩
    rw [hg] at hm
    exact hm

/-- Every actual integral section stabilizer fixes its actual real matrix projection. -/
theorem generatedAxisE8_section_stabilizer_matrix_action (c : Fin 24 → ZMod 2)
    (g : leechIsomSubgroup)
    (hg : generatedAxisE8ImageSection g c = generatedAxisE8CoordinateSection c) :
    conwayMatrixAction g (Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1)) =
      Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1) :=
  generatedAxisE8_preserving_matrix_action c g (generatedAxisE8_preserves_of_image_eq c g hg)

/-- Stabilizing the actual coordinate E8 section fixes the actual octad-image axis matrix. -/
theorem generatedAxisE8_octad_stabilizer_axis_matrix
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (g : leechIsomSubgroup)
    (hg : generatedAxisE8ImageSection g (golayOctadWord o) =
      generatedAxisE8CoordinateSection (golayOctadWord o)) :
    conwayMatrixAction g
      (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).1 =
      (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).1 := by
  have hd : Matrix.diagonal (fun i => if golayOctadWord o i = 0 then (0 : ℝ) else 1) =
      (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).1 := by
    rw [generatedAxis_triality_octad_matrix]
    congr 1
    funext i
    have hi : golayOctadWord o i ≠ 0 ↔
        (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true := by
      simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
        Finset.mem_univ, true_and] using golayOctadWord_ne_zero_iff o i
    by_cases hb : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true
    · simp [hb, hi.mpr hb]
    · have hz : golayOctadWord o i = 0 := by
        by_contra hn
        exact hb (hi.mp hn)
      simp [hz, hb]
  rw [← hd]
  exact generatedAxisE8_section_stabilizer_matrix_action (golayOctadWord o) g hg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
