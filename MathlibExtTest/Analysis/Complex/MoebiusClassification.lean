/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.MoebiusClassification

set_option autoImplicit false

open Matrix Moebius OnePoint

namespace MoebiusClassificationTest

/-! ### The trace criteria on standard examples -/

-- The translation `z ↦ z + 1` is parabolic: `tr ^ 2 - 4 * det = 4 - 4 = 0`.
example : IsParabolic (GeneralLinearGroup.mkOfDetNeZero !![(1 : ℂ), 1; 0, 1] (by simp)) := by
  rw [isParabolic_iff_discr_eq_zero]
  norm_num [discr_fin_two, trace_fin_two, det_fin_two]

-- The dilation `z ↦ 2 * z` is strictly hyperbolic (`tr ^ 2 / det = 9 / 2 > 4`) and not
-- parabolic (`tr ^ 2 - 4 * det = 1`).
example :
    IsStrictlyHyperbolic (GeneralLinearGroup.mkOfDetNeZero !![(2 : ℂ), 0; 0, 1] (by simp)) ∧
      ¬IsParabolic (GeneralLinearGroup.mkOfDetNeZero !![(2 : ℂ), 0; 0, 1] (by simp)) := by
  rw [isStrictlyHyperbolic_iff_trace_sq_div_det, isParabolic_iff_discr_eq_zero]
  refine ⟨⟨9 / 2, by norm_num, ?_⟩, ?_⟩ <;>
    norm_num [discr_fin_two, trace_fin_two, det_fin_two]

-- The rotation `z ↦ I * z` is elliptic: `tr ^ 2 / det = (I + 1) ^ 2 / I = 2`.
example : IsElliptic (GeneralLinearGroup.mkOfDetNeZero !![Complex.I, 0; 0, 1] (by simp)) := by
  rw [isElliptic_iff_trace_sq_div_det]
  refine ⟨2, by norm_num, by norm_num, ?_⟩
  simp only [GeneralLinearGroup.val_mkOfDetNeZero, trace_fin_two_of, det_fin_two_of]
  rw [div_eq_iff (by simp)]
  push_cast
  linear_combination Complex.I_sq

/-! ### The boundary values `4` and `0` of `tr ^ 2 / det` -/

-- The identity has `tr ^ 2 / det = 4`. It is parabolic, and it has the multiplier `1`, whose norm
-- is `1`, but it is neither strictly hyperbolic nor elliptic.
example : IsParabolic (1 : GL (Fin 2) ℂ) ∧ IsMultiplier 1 1 ∧
    ¬IsStrictlyHyperbolic (1 : GL (Fin 2) ℂ) ∧ ¬IsElliptic (1 : GL (Fin 2) ℂ) ∧
    (1 : GL (Fin 2) ℂ).val.trace ^ 2 / (1 : GL (Fin 2) ℂ).val.det = 4 := by
  have h4 : (1 : GL (Fin 2) ℂ).val.trace ^ 2 / (1 : GL (Fin 2) ℂ).val.det = 4 := by
    norm_num [trace_fin_two, det_fin_two]
  refine ⟨Or.inl fun x ↦ one_smul _ x, ⟨1, fun x ↦ by cases x <;> simp⟩, ?_, ?_, h4⟩
  · rw [isStrictlyHyperbolic_iff_trace_sq_div_det, h4]
    rintro ⟨r, hr, h⟩
    have : r = 4 := by exact_mod_cast h.symm
    linarith
  · rw [isElliptic_iff_trace_sq_div_det, h4]
    rintro ⟨r, -, hr, h⟩
    have : r = 4 := by exact_mod_cast h.symm
    linarith

/-- The half-turn `z ↦ -z`. -/
noncomputable def halfTurn : GL (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, -1] (by simp)

-- The half-turn has `tr ^ 2 / det = 0`, the other end of the elliptic range, and its multiplier
-- is `-1`, with fixed points `0` and `∞` (here `T` is the identity).
example : IsMultiplier halfTurn (-1) ∧ IsElliptic halfTurn := by
  refine ⟨⟨1, fun x ↦ ?_⟩, ?_⟩
  · cases x with
    | infty => simp [halfTurn, smul_infty_eq_ite]
    | coe z => simp [halfTurn, smul_some_eq_ite, div_neg]
  · rw [isElliptic_iff_trace_sq_div_det]
    exact ⟨0, le_rfl, by norm_num, by simp [halfTurn, trace_fin_two]⟩

/-! ### The normal form (12) for a map with two finite fixed points -/

/-- `S z = 2 z / (z + 1)`. Its fixed points are `0` and `1`; it sends its pole `-1` to `∞` and
`∞` to `2`. -/
noncomputable def S : GL (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero !![2, 0; 1, 1] (by norm_num [det_fin_two])

/-- `T z = z / (z - 1)`, the map `(z - α) / (z - β)` of (12) for `α = 0` and `β = 1`. -/
noncomputable def T : GL (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, -1] (by norm_num [det_fin_two])

/-- A direct multiplier witness on the whole sphere: `T (S x) = 2 * T x` for every `x`, including
the pole `-1` of `S`, the pole `1` of `T` and `∞`. -/
theorem isMultiplier_S : IsMultiplier S 2 := by
  refine ⟨T, fun x ↦ ?_⟩
  cases x with
  | infty => norm_num [S, T, smul_infty_eq_ite, smul_some_eq_ite]
  | coe z =>
    by_cases h1 : z = -1
    · subst h1
      norm_num [S, T, smul_infty_eq_ite, smul_some_eq_ite]
    by_cases h2 : z = 1
    · subst h2
      norm_num [S, T, smul_infty_eq_ite, smul_some_eq_ite]
    have h1' : z + 1 ≠ 0 := fun h ↦ h1 (eq_neg_of_add_eq_zero_left h)
    have h2' : z - 1 ≠ 0 := sub_ne_zero.2 h2
    have h4 : 2 * z - (z + 1) ≠ 0 := by
      contrapose! h2
      linear_combination h2
    have h3 : 2 * z / (z + 1) - 1 ≠ 0 := by
      rw [div_sub_one h1']
      exact div_ne_zero h4 h1'
    have hSz : S • (z : OnePoint ℂ) = ↑(2 * z / (z + 1)) := by
      simp [S, smul_some_eq_ite, h1']
    have hT (w : ℂ) (hw : w - 1 ≠ 0) : T • (w : OnePoint ℂ) = ↑(w / (w - 1)) := by
      simp [T, smul_some_eq_ite, ← sub_eq_add_neg, hw]
    rw [hSz, hT _ h3, hT _ h2', OnePoint.map_some, OnePoint.coe_eq_coe, div_sub_one h1']
    field_simp
    ring

/-- The fixed points of `S` are `0` and `1`. -/
theorem eq_zero_or_eq_one_of_smul_S_eq {x : OnePoint ℂ} (hx : S • x = x) :
    x = ((0 : ℂ) : OnePoint ℂ) ∨ x = ((1 : ℂ) : OnePoint ℂ) := by
  cases x with
  | infty => simp [S, smul_infty_eq_ite] at hx
  | coe z =>
    simp only [S, smul_some_eq_ite, GeneralLinearGroup.val_mkOfDetNeZero, of_apply, cons_val',
      cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, one_mul, add_zero] at hx
    split_ifs at hx with h
    · exact absurd hx (OnePoint.infty_ne_coe _)
    · rw [OnePoint.coe_eq_coe, div_eq_iff h] at hx
      have : z * (z - 1) = 0 := by linear_combination -hx
      rcases mul_eq_zero.1 this with h0 | h0
      · exact Or.inl (by rw [h0])
      · exact Or.inr (by rw [sub_eq_zero.1 h0])

-- The literal normal form (12) for `S` with `α = 0`, `β = 1`, `k = 2`, obtained from the witness
-- through `isMultiplier_iff` and `sub_div_sub_eq_mul_sub_div_sub`:
-- `(w - 0) / (w - 1) = 2 * (z - 0) / (z - 1)` for `w = S z`.
example {z : ℂ} (hz1 : z ≠ 1) (hz : z ≠ -1) :
    (2 * z / (z + 1) - 0) / (2 * z / (z + 1) - 1) = 2 * ((z - 0) / (z - 1)) := by
  have hz' : z + 1 ≠ 0 := fun h ↦ hz (eq_neg_of_add_eq_zero_left h)
  have hw (z : ℂ) (hz : z + 1 ≠ 0) : S • (z : OnePoint ℂ) = ↑(2 * z / (z + 1)) := by
    simp [S, smul_some_eq_ite, hz]
  obtain ⟨α, β, hne, hα, hβ, hT⟩ := isMultiplier_iff.1 isMultiplier_S
  rcases eq_zero_or_eq_one_of_smul_S_eq hα with rfl | rfl <;>
    rcases eq_zero_or_eq_one_of_smul_S_eq hβ with rfl | rfl
  · exact absurd rfl hne
  · exact sub_div_sub_eq_mul_sub_div_sub zero_ne_one hT hz1 (hw z hz')
  · -- The other order of the fixed points would give `1 / 4 = 1` at `z = 2`.
    have := sub_div_sub_eq_mul_sub_div_sub one_ne_zero hT two_ne_zero (hw 2 (by norm_num))
    norm_num at this
  · exact absurd rfl hne

end MoebiusClassificationTest

#print axioms classification_by_trace
#print axioms isMultiplier_iff
#print axioms sub_div_sub_eq_mul_sub_div_sub
