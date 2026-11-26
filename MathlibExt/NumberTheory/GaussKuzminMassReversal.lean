/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GaussKuzminFundamentalIntervals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reversal symmetry of the Gauss–Kuzmin mass

Integrating the Gauss–Kuzmin density over a fundamental interval gives a logarithmic ratio.
Writing the ratio as $1 + (-1)^n / D$, the denominator $D$ is the product of the bottom-row and
right-column sums of the convergent matrix, which are interchanged by reversal.
-/

namespace MetaMathlibExt

open MeasureTheory Real Set

private theorem convergentMatrix_bounds (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    0 ≤ convergentMatrix a 0 0 ∧ 0 ≤ convergentMatrix a 0 1 ∧
      0 ≤ convergentMatrix a 1 0 ∧ 1 ≤ convergentMatrix a 1 1 ∧
      (a ≠ [] → 1 ≤ convergentMatrix a 0 1) := by
  induction a with
  | nil => simp [convergentMatrix_nil]
  | cons t a ih =>
    have ht : 1 ≤ t := ha t List.mem_cons_self
    have ht' : (1 : ℤ) ≤ t := by exact_mod_cast ht
    have ha' : ∀ x ∈ a, 0 < x := fun x hx => ha x (List.mem_cons_of_mem t hx)
    obtain ⟨h00, h01, h10, h11, -⟩ := ih ha'
    rw [(convergentMatrix_reverse_append_cons a ha' t ht).2.2.1]
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, ne_eq, reduceCtorEq, not_false_eq_true,
      forall_const]
    refine ⟨h10, by omega, by positivity, ?_, h11⟩
    have hmul : convergentMatrix a 1 1 ≤ t * convergentMatrix a 1 1 :=
      le_mul_of_one_le_left (by omega) ht'
    omega

private theorem integral_fundInterval_one_div {u v : ℝ} (hu : 0 < 1 + u) (hv : 0 < 1 + v) :
    (∫ x in fundInterval u v, 1 / (1 + x)) = |log ((1 + v) / (1 + u))| := by
  have hset : (∫ x in fundInterval u v, 1 / (1 + x)) = ∫ x in uIoc u v, 1 / (1 + x) := by
    rcases lt_or_ge u v with h | h
    · rw [fundInterval_of_lt h, uIoc_of_le h.le, integral_Ico_eq_integral_Ioc]
    · rw [fundInterval, ite_eq_right (not_lt_of_ge h), uIoc_of_ge h]
  have hnonneg : 0 ≤ ∫ x in uIoc u v, 1 / (1 + x) := by
    refine setIntegral_nonneg measurableSet_uIoc fun x hx => ?_
    have hx' : min u v < x := hx.1
    have hmin : -(1 : ℝ) < min u v := lt_min (by linarith) (by linarith)
    have : 0 < 1 + x := by linarith [hmin.trans hx']
    positivity
  rw [hset, ← abs_of_nonneg hnonneg, ← intervalIntegral.abs_integral_eq_abs_integral_uIoc]
  congr 1
  simpa only [one_div] using
    (intervalIntegral.integral_comp_add_left (a := u) (b := v) (fun x : ℝ => x⁻¹) 1).trans
      (integral_inv_of_pos hu hv)

private theorem integral_fundInterval_convergent {p r q s : ℝ}
    (hp : 1 ≤ p) (hr : 0 ≤ r) (hq : 1 ≤ q) (hs : -1 ≤ s) :
    (∫ x in fundInterval (r / q) (r / q + s / (q * (p + q))), 1 / (1 + x)) =
      |log (1 + s / ((p + q) * (r + q)))| := by
  have hqPos : 0 < q := by linarith
  have hpq : 0 < p + q := by linarith
  have hrq : 0 < r + q := by linarith
  have hu : 0 < 1 + r / q := by positivity
  have hden : 1 < q * (p + q) :=
    (show 1 < p + q by linarith).trans_le (le_mul_of_one_le_left hpq.le hq)
  have hδ : -1 < s / (q * (p + q)) := (lt_div_iff₀ (lt_trans zero_lt_one hden)).2 (by linarith)
  have hv : 0 < 1 + (r / q + s / (q * (p + q))) := by
    linarith [div_nonneg hr hqPos.le]
  rw [integral_fundInterval_one_div hu hv]
  congr 2
  field_simp
  ring

private theorem gaussKuzminMass_reverse_eq (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) (hne : a ≠ []) :
    gaussKuzminMass a.reverse = |log (1 + (-1) ^ a.length /
      (((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ)) *
        ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ))))| / log 2 := by
  obtain ⟨-, -, hr, hq, hp⟩ := convergentMatrix_bounds a ha
  have hs : (-1 : ℝ) ≤ (-1) ^ a.length := by
    have h : |(-1 : ℝ) ^ a.length| = 1 := by simp
    simpa only [h] using neg_abs_le ((-1 : ℝ) ^ a.length)
  rw [gaussKuzminMass, setIntegral_congr_set (cfCylinder_reverse_append_cons_ae_eq a ha 1 le_rfl).1,
    integral_fundInterval_convergent (by exact_mod_cast hp hne) (by exact_mod_cast hr)
      (by exact_mod_cast hq) hs]

/-- **Reversal symmetry of the Gauss–Kuzmin mass.** For every string $a$ of positive integers,
$P_{GK}(\overleftarrow{a}) = P_{GK}(a)$, where $P_{GK}$ is the Gauss–Kuzmin mass and
$\overleftarrow{a}$ is the reverse of $a$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Proposition 1.3 (`integers-2025-A89-prop-1-3`), equations (1.8) and (1.9). -/
public theorem gaussKuzminMass_reverse (a : List ℕ) (ha : (∀ x ∈ a, 0 < x)) :
    gaussKuzminMass a.reverse = gaussKuzminMass a := by
  by_cases hnil : a = []
  · subst a
    rfl
  have ha' : ∀ x ∈ a.reverse, 0 < x := fun x hx => ha x (List.mem_reverse.mp hx)
  have h := gaussKuzminMass_reverse_eq a.reverse ha' (by simpa using hnil)
  -- The transpose swaps the two sums in the denominator.
  rw [List.reverse_reverse, List.length_reverse,
    (convergentMatrix_reverse_append_cons a ha 1 le_rfl).1] at h
  rw [gaussKuzminMass_reverse_eq a ha hnil, h]
  simp [mul_comm]

end MetaMathlibExt
