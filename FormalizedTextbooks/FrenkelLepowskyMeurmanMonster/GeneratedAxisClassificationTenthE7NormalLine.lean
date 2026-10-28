/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitE8Section
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitProjection

/-! Every actual whole matrix fixer preserves the original standard normal root up to sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- All twenty-four actual coordinates of the original standard normal root. -/
theorem generatedTenth_e7_normal_root_coordinate (i : Fin 24) :
    generatedTenthE7OrbitNormalRoot.val i = if i = 4 ∨ i = 5 then 4 else 0 := by
  fin_cases i <;> rfl

/-- The original normal root belongs to the whole standard E8 section. -/
theorem generatedTenth_e7_normal_root_section :
    generatedTenthE7OrbitNormalRoot ∈ generatedTenthE7StandardE8Section := by
  rw [generatedTenth_e7_standard_e8_section_mem]
  intro i hi
  rw [generatedTenth_e7_normal_root_coordinate]
  have h4 : i ≠ 4 := by intro h; subst i; norm_num at hi
  have h5 : i ≠ 5 := by intro h; subst i; norm_num at hi
  simp only [h4, h5, false_or, ite_false]

/-- The original normal root has integer square sum32. -/
theorem generatedTenth_e7_normal_root_square :
    leechSquareSum generatedTenthE7OrbitNormalRoot.val = 32 := by
  decide +kernel

/-- The original normal root is in the entire actual projector kernel. -/
theorem generatedTenth_e7_normal_root_projector_zero :
    generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ
      leechCoordinateEmbedding generatedTenthE7OrbitNormalRoot.val = 0 := by
  ext i
  rw [generatedTenth_e7_root_orbit_projector_coordinate]
  fin_cases i <;>
    norm_num [leechCoordinateEmbedding, generatedTenth_e7_normal_root_coordinate]
  all_goals ring

/-- The actual integral kernel inside the standard E8 section is precisely its normal line. -/
theorem generatedTenth_e7_section_kernel_shape (u : leechIntegral)
    (hu : u ∈ generatedTenthE7StandardE8Section)
    (hp : generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ
      leechCoordinateEmbedding u.val = 0) :
    u.val = fun i => if i = 4 ∨ i = 5 then u.val 4 else 0 := by
  have hs := (generatedTenth_e7_standard_e8_section_mem u).mp hu
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  have h45 : u.val 4 = u.val 5 := by
    have h := congrFun hp 4
    rw [generatedTenth_e7_root_orbit_projector_coordinate] at h
    norm_num only [Fin.val_ofNat, show (4 : ℕ) < 8 by decide,
      ite_true, true_or, Pi.zero_apply] at h
    change 2 * ((u.val 4 : ℝ) / Real.sqrt 8) -
      ((u.val 4 : ℝ) / Real.sqrt 8 + (u.val 5 : ℝ) / Real.sqrt 8) = 0 at h
    field_simp [hsqrt] at h
    exact_mod_cast (by linarith : (u.val 4 : ℝ) = (u.val 5 : ℝ))
  funext i
  by_cases hi : i = 4 ∨ i = 5
  · rw [ite_eq_left hi]
    rcases hi with rfl | rfl
    · rfl
    · exact h45.symm
  · rw [ite_eq_right hi]
    by_cases h8 : i.val < 8
    · have h := congrFun hp i
      rw [generatedTenth_e7_root_orbit_projector_coordinate] at h
      simp only [ite_eq_left h8, ite_eq_right hi, sub_zero, Pi.zero_apply] at h
      change 2 * ((u.val i : ℝ) / Real.sqrt 8) = 0 at h
      have hv : (u.val i : ℝ) / Real.sqrt 8 = 0 := by linarith
      have hz : (u.val i : ℝ) = 0 := by
        simpa only [div_eq_zero_iff, hsqrt, or_false] using hv
      exact_mod_cast hz
    · exact hs i (Nat.le_of_not_gt h8)

/-- A square-sum32 vector on this entire actual kernel line is one of its two orientations. -/
theorem generatedTenth_e7_section_kernel_short (u : leechIntegral)
    (hu : u ∈ generatedTenthE7StandardE8Section)
    (hp : generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ
      leechCoordinateEmbedding u.val = 0)
    (hn : leechSquareSum u.val = 32) :
    u = generatedTenthE7OrbitNormalRoot ∨ u = -generatedTenthE7OrbitNormalRoot := by
  have hf := generatedTenth_e7_section_kernel_shape u hu hp
  have hsum : leechSquareSum u.val = 2 * (u.val 4) ^ 2 := by
    rw [hf]
    norm_num [leechSquareSum, Fin.sum_univ_succ]
    ring
  have ha : u.val 4 = 4 ∨ u.val 4 = -4 := by
    have hmul : (u.val 4 - 4) * (u.val 4 + 4) = 0 := by nlinarith [hn, hsum]
    rcases mul_eq_zero.mp hmul with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases ha with ha | ha
  · left
    apply Subtype.ext
    funext i
    rw [congrFun hf i, ha, generatedTenth_e7_normal_root_coordinate]
  · right
    apply Subtype.ext
    funext i
    change u.val i = -generatedTenthE7OrbitNormalRoot.val i
    rw [congrFun hf i, ha, generatedTenth_e7_normal_root_coordinate]
    split_ifs <;> rfl

/-- Every member of the entire actual standard matrix group preserves the normal root line. -/
theorem generatedTenth_e7_matrix_normal_line (g : generatedTenthE7StandardMatrixGroup) :
    leechIntegralAction g.val generatedTenthE7OrbitNormalRoot = generatedTenthE7OrbitNormalRoot ∨
      leechIntegralAction g.val generatedTenthE7OrbitNormalRoot =
        -generatedTenthE7OrbitNormalRoot := by
  apply generatedTenth_e7_section_kernel_short
  · exact (generatedTenth_e7_root_orbit_e8_section g _).mp
      generatedTenth_e7_normal_root_section
  · rw [leechIntegralAction_embedding, ← generatedTenth_e7_root_orbit_standard_commute,
      generatedTenth_e7_normal_root_projector_zero, map_zero]
  · rw [leechIntegralAction_squareSum, generatedTenth_e7_normal_root_square]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
