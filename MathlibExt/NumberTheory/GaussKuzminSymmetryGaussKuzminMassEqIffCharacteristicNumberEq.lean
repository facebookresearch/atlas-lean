/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GaussKuzminSymmetry
import MathlibExt.NumberTheory.GaussKuzminFundamentalIntervals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Equality of Gauss–Kuzmin masses and characteristic numbers

This module proves that positive digit strings of the same length parity have equal
Gauss–Kuzmin masses exactly when their characteristic numbers agree.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.2.
-/

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory Real

private theorem matrix_bounds (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    (∀ i j, 0 ≤ convergentMatrix a i j) ∧ 1 ≤ convergentMatrix a 1 1 := by
  induction a with
  | nil => simp [convergentMatrix_nil, Matrix.one_apply]
  | cons t a ih =>
    obtain ⟨hn, hq⟩ := ih (fun x hx => ha x (List.mem_cons_of_mem t hx))
    have ht : (1 : ℤ) ≤ t := by exact_mod_cast ha t List.mem_cons_self
    rw [convergentMatrix_cons]
    constructor
    · intro i j
      have h0 := hn 0 j
      have h1 := hn 1 j
      fin_cases i
      · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h1
      · simpa [Matrix.mul_apply, Fin.sum_univ_two] using
          (show 0 ≤ convergentMatrix a 0 j + t * convergentMatrix a 1 j by positivity)
    · suffices 1 ≤ convergentMatrix a 0 1 + t * convergentMatrix a 1 1 by
        simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
      nlinarith [hn 0 1]

private theorem integral_fundInterval (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (∫ x in fundInterval u v, 1 / (1 + x)) =
      if u < v then log ((1 + v) / (1 + u)) else -log ((1 + v) / (1 + u)) := by
  have hint : (∫ x in u..v, 1 / (1 + x)) = log ((1 + v) / (1 + u)) := by
    rw [intervalIntegral.integral_comp_add_left (fun x : ℝ => 1 / x) 1]
    exact integral_one_div_of_pos (by positivity) (by positivity)
  by_cases huv : u < v
  · rw [ite_eq_left huv, fundInterval_of_lt huv, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le huv.le, hint]
  · rw [ite_eq_right huv, fundInterval, ite_eq_right huv,
      ← intervalIntegral.integral_of_le (le_of_not_gt huv),
      intervalIntegral.integral_symm, hint]

private theorem endpoint_nonneg (p q r : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ p / q + (-1) ^ n / (q * (r + q)) := by
  have he : (-1 : ℝ) ≤ (-1) ^ n := by
    rcases neg_one_pow_eq_or ℝ n with h | h <;> simp [h]
  have hnum : 0 ≤ p * (r + q) + (-1) ^ n := by nlinarith
  calc
    0 ≤ (p * (r + q) + (-1) ^ n) / (q * (r + q)) := by positivity
    _ = p / q + (-1) ^ n / (q * (r + q)) := by
      have hq0 : q ≠ 0 := by positivity
      have hsum : r + q ≠ 0 := by positivity
      field_simp

private theorem cylinder_ae (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    cfCylinder a =ᵐ[volume]
      fundInterval ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ))
        ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) +
          (-1) ^ a.length / ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ)))) := by
  have hrev : ∀ x ∈ a.reverse, 0 < x := by simpa only [List.mem_reverse] using ha
  have h := (cfCylinder_reverse_append_cons_ae_eq a.reverse hrev 1 (by decide)).1
  have hmat := (convergentMatrix_reverse_append_cons a ha 1 (by decide)).1
  simpa [hmat] using h

private theorem mass_formula (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    0 < (characteristicNumber a : ℝ) ∧
      0 < 1 + (-1 : ℝ) ^ a.length / (characteristicNumber a : ℝ) ∧
      gaussKuzminMass a =
        (if 0 < (-1 : ℝ) ^ a.length then
          log (1 + (-1 : ℝ) ^ a.length / (characteristicNumber a : ℝ)) else
          -log (1 + (-1 : ℝ) ^ a.length / (characteristicNumber a : ℝ))) / log 2 := by
  let p : ℝ := convergentMatrix a 0 1
  let q : ℝ := convergentMatrix a 1 1
  let r : ℝ := convergentMatrix a 1 0
  let e : ℝ := (-1) ^ a.length
  let u := p / q
  let v := u + e / (q * (r + q))
  let c : ℝ := characteristicNumber a
  obtain ⟨hn, hq⟩ := matrix_bounds a ha
  have hp0 : 0 ≤ p := by
    dsimp [p]
    exact_mod_cast hn 0 1
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact_mod_cast hn 1 0
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast hq
  have hq0 : q ≠ 0 := by positivity
  have hsum : r + q ≠ 0 := by positivity
  have hpq : p + q ≠ 0 := by positivity
  have hc : c = (p + q) * (r + q) := by simp [c, p, q, r, characteristicNumber]
  have hc0 : 0 < c := by rw [hc]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by
    cases a with
    | nil => simp [v, u, p, q, r, e, convergentMatrix_nil]
    | cons t a =>
      have htail : ∀ x ∈ a, 0 < x := fun x hx => ha x (List.mem_cons_of_mem t hx)
      have hp1 : (1 : ℤ) ≤ convergentMatrix (t :: a) 0 1 := by
        rw [convergentMatrix_cons]
        simpa [Matrix.mul_apply, Fin.sum_univ_two] using (matrix_bounds a htail).2
      exact endpoint_nonneg p q r (by dsimp [p]; exact_mod_cast hp1) hq1 hr0 (t :: a).length
  have hratio : (1 + v) / (1 + u) = 1 + e / c := by
    rw [hc]
    dsimp [v, u]
    field_simp
    ring
  have horder : u < v ↔ 0 < e := by
    dsimp [v]
    rw [lt_add_iff_pos_right, div_pos_iff_of_pos_right (by positivity)]
  refine ⟨hc0, ?_, ?_⟩
  · change 0 < 1 + e / c
    rw [← hratio]
    positivity
  · rw [gaussKuzminMass, setIntegral_congr_set (cylinder_ae a ha),
      integral_fundInterval u v hu hv]
    simp only [horder, hratio, e, c]

/-- **Gauss–Kuzmin masses agree exactly when characteristic numbers do.** Write $P_{GK}$ for the
Gauss–Kuzmin mass and $\chi$ for the characteristic number of a string. If $a$ and $b$ are strings
of positive integers whose lengths have the same parity, then $P_{GK}(a) = P_{GK}(b)$ if and only
if $\chi(a) = \chi(b)$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.2 (`integers-2025-A89-lem-5-2`). -/
public theorem gaussKuzminMass_eq_iff_characteristicNumber_eq (a b : List ℕ)
    (ha : (∀ x ∈ a, 0 < x)) (hb : ∀ x ∈ b, 0 < x) (hpar : a.length % 2 = b.length % 2) :
    gaussKuzminMass a = gaussKuzminMass b ↔ characteristicNumber a = characteristicNumber b := by
  obtain ⟨hca, hra, hfa⟩ := mass_formula a ha
  obtain ⟨hcb, hrb, hfb⟩ := mass_formula b hb
  have he : (-1 : ℝ) ^ a.length = (-1) ^ b.length := by
    rw [neg_one_pow_eq_pow_mod_two a.length, neg_one_pow_eq_pow_mod_two b.length, hpar]
  rw [← he] at hrb
  rw [hfa, hfb, ← he]
  constructor
  · intro h
    have hl := (div_left_inj₀ (ne_of_gt (log_pos (by norm_num : (1 : ℝ) < 2)))).mp h
    have hlogs : log (1 + (-1 : ℝ) ^ a.length / (characteristicNumber a : ℝ)) =
        log (1 + (-1 : ℝ) ^ a.length / (characteristicNumber b : ℝ)) := by
      split_ifs at hl <;> linarith
    have hr := log_injOn_pos hra hrb hlogs
    have hf : (-1 : ℝ) ^ a.length / (characteristicNumber a : ℝ) =
        (-1 : ℝ) ^ a.length / (characteristicNumber b : ℝ) := by linarith
    have hc := (div_eq_div_iff (ne_of_gt hca) (ne_of_gt hcb)).mp hf
    have he0 : (-1 : ℝ) ^ a.length ≠ 0 := pow_ne_zero _ (by norm_num)
    have hcast := (mul_left_cancel₀ he0 hc).symm
    exact_mod_cast hcast
  · intro h
    rw [h]

end

end MetaMathlibExt
