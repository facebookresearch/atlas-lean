/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPhysicalMatrices

/-! Exact integer prefix certificates bind arbitrary full original spatial source words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- An absent next source letter denotes the identity with the same denominator two. -/
def generatedTwelfthSpatialPrefixStep (w : List (Fin 18 × Bool)) (k : ℕ) :
    Matrix (Fin 24) (Fin 24) ℤ :=
  ((w[k]?).map generatedTwelfthSectionPhysicalNumerator).getD ((2 : ℕ) • 1)

/-- Every optional complete source letter retains its actual whole physical matrix. -/
theorem generatedTwelfth_spatial_optional_matrix (o : Option (Fin 18 × Bool)) :
    ((o.map generatedTwelfthSectionPhysicalNumerator).getD ((2 : ℕ) • 1)).map
      (Int.castRingHom ℝ) =
      (2 : ℝ) • leechIsomMatrix ((o.toList.map generatedTwelfthRootOrbitLetter).prod).val := by
  cases o with
  | none =>
    simp only [Option.map_none, Option.getD_none, Option.toList_none, List.map_nil,
      List.prod_nil, Subgroup.coe_one, generatedTwelfth_section_physical_matrix_one]
    rw [two_nsmul]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> norm_num
  | some l =>
    simp only [Option.map_some, Option.getD_some, Option.toList_some, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [generatedTwelfth_section_physical_letter_matrix, smul_smul]
    norm_num

/-- Every checked complete integer prefix is the actual entire source isometry at that prefix. -/
theorem generatedTwelfth_spatial_prefix_actual_of_certificates
    (w : List (Fin 18 × Bool)) (a : ℕ → Matrix (Fin 24) (Fin 24) ℤ) (d : ℕ → ℕ)
    (ha0 : a 0 = 1) (hd0 : d 0 = 1)
    (hstep : ∀ k < w.length,
      d (k + 1) • (a k * generatedTwelfthSpatialPrefixStep w k) =
        (2 * d k) • a (k + 1))
    (hd : ∀ k ≤ w.length, d k ≠ 0) (k : ℕ) (hk : k ≤ w.length) :
    (a k).map (Int.castRingHom ℝ) =
      (d k : ℝ) • leechIsomMatrix
        (((w.take k).map generatedTwelfthRootOrbitLetter).prod).val := by
  induction k with
  | zero =>
    rw [ha0, hd0, List.take_zero, List.map_nil, List.prod_nil, Subgroup.coe_one,
      generatedTwelfth_section_physical_matrix_one]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, apply_ite]
  | succ k ih =>
    have hlt : k < w.length := by omega
    have hi := ih (by omega)
    have hr := congrArg (Int.castRingHom ℝ).mapMatrix (hstep k hlt)
    simp only [map_nsmul, map_mul] at hr
    change d (k + 1) • ((a k).map (Int.castRingHom ℝ) *
        (generatedTwelfthSpatialPrefixStep w k).map (Int.castRingHom ℝ)) =
      (2 * d k) • (a (k + 1)).map (Int.castRingHom ℝ) at hr
    rw [hi, generatedTwelfthSpatialPrefixStep,
      generatedTwelfth_spatial_optional_matrix] at hr
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul] at hr
    rw [List.take_add_one, List.map_append, List.prod_append, Subgroup.coe_mul,
      generatedTwelfth_matrix_fixer_matrix_mul]
    ext i j
    have hc := congrFun (congrFun hr i) j
    simp only [Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul] at hc
    have hn : (2 * (d k : ℝ)) ≠ 0 := mul_ne_zero (by norm_num) (by
      exact_mod_cast hd k (by omega))
    apply mul_left_cancel₀ hn
    simp only [Nat.cast_mul, Nat.cast_ofNat, Matrix.map_apply,
      Matrix.smul_apply, smul_eq_mul] at hc ⊢
    linear_combination -hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
