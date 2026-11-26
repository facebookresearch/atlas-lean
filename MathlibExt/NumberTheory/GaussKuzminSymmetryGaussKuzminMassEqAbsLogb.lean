/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import MathlibExt.NumberTheory.GaussKuzminSymmetry
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.GaussKuzminFundamentalIntervals

/-!
# Explicit Gauss–Kuzmin mass of a string

This module proves that the Gauss–Kuzmin mass of a string of positive integers equals the
Gauss–Kuzmin mass of its reverse and equals the absolute value of an explicit base-two logarithm
in the entries of its convergent matrix.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 2.5 (`integers-2025-A89-lem-2-5`), equation (2.13).
-/

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory Filter Topology Real

-- Entry formulas for prepending a digit.
private theorem cm_cons_00 (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 0 0 = convergentMatrix a 1 0 := by
  rw [convergentMatrix_cons]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cm_cons_01 (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 0 1 = convergentMatrix a 1 1 := by
  rw [convergentMatrix_cons]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cm_cons_10 (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 1 0 = convergentMatrix a 0 0 + t * convergentMatrix a 1 0 := by
  rw [convergentMatrix_cons]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cm_cons_11 (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 1 1 = convergentMatrix a 0 1 + t * convergentMatrix a 1 1 := by
  rw [convergentMatrix_cons]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

-- Entries of convergent matrices of positive strings are nonnegative, with `q ≥ 1`.
private theorem cm_entries_nonneg (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    0 ≤ convergentMatrix a 0 0 ∧ 0 ≤ convergentMatrix a 0 1 ∧
    0 ≤ convergentMatrix a 1 0 ∧ 1 ≤ convergentMatrix a 1 1 := by
  induction a with
  | nil => simp [convergentMatrix_nil]
  | cons t a ih =>
    have ht : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ha t (by simp)
    have ht0 : (0 : ℤ) ≤ (t : ℤ) := by exact_mod_cast Nat.zero_le t
    have ha' : ∀ x ∈ a, 0 < x := fun x hx => ha x (by simp [hx])
    obtain ⟨h00, h01, h10, h11⟩ := ih ha'
    rw [cm_cons_00, cm_cons_01, cm_cons_10, cm_cons_11]
    refine ⟨h10, zero_le_one.trans h11, by positivity, by nlinarith [h01, ht, h11]⟩

-- The upper-right entry is positive for nonempty positive strings.
private theorem cm_01_of_ne_nil (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) (hne : a ≠ []) :
    1 ≤ convergentMatrix a 0 1 := by
  obtain ⟨t, as, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [cm_cons_01]
  exact (cm_entries_nonneg as (fun x hx => ha x (by simp [hx]))).2.2.2

-- The lower-left entry is positive for nonempty positive strings.
private theorem cm_10_of_ne_nil (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) (hne : a ≠ []) :
    1 ≤ convergentMatrix a 1 0 := by
  have ha_rev : ∀ x ∈ a.reverse, 0 < x := fun x hx => ha x (List.mem_reverse.mp hx)
  have h01 := cm_01_of_ne_nil a.reverse ha_rev (List.reverse_ne_nil_iff.mpr hne)
  have hm := (convergentMatrix_reverse_append_cons a ha 1 (le_refl 1)).1
  have e : convergentMatrix a.reverse 0 1 = convergentMatrix a 1 0 := by rw [hm]; simp
  rw [← e]
  exact h01

-- The fundamental interval of a string is almost everywhere the half-open interval between
-- its convergent endpoints written with the determinant offset.
private theorem cyl_ae (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    cfCylinder a =ᵐ[volume] fundInterval
      ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ))
      ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
        ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 1 0 : ℝ) +
          (convergentMatrix a 1 1 : ℝ)))) := by
  have ha_rev : ∀ x ∈ a.reverse, 0 < x := fun x hx => ha x (List.mem_reverse.mp hx)
  have h := (cfCylinder_reverse_append_cons_ae_eq a.reverse ha_rev 1 (le_refl 1)).1
  rw [List.reverse_reverse, List.length_reverse] at h
  have hm := (convergentMatrix_reverse_append_cons a ha 1 (le_refl 1)).1
  have e10 : convergentMatrix a.reverse 1 0 = convergentMatrix a 0 1 := by rw [hm]; simp
  have e11 : convergentMatrix a.reverse 1 1 = convergentMatrix a 1 1 := by rw [hm]; simp
  have e01 : convergentMatrix a.reverse 0 1 = convergentMatrix a 1 0 := by rw [hm]; simp
  rw [e10, e11, e01] at h
  exact h

-- The Gauss–Kuzmin integral over a half-open interval is an absolute base-two logarithm.
private theorem fundInterval_integral (α β : ℝ) (h1α : (0 : ℝ) < 1 + α) (h1β : (0 : ℝ) < 1 + β) :
    (∫ x in fundInterval α β, 1 / (1 + x)) / log 2 = |logb 2 ((1 + β) / (1 + α))| := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  have h_int : (∫ x in α..β, (1 : ℝ) / (1 + x)) = log ((1 + β) / (1 + α)) := by
    have hsub : (∫ x in α..β, (fun u : ℝ => u⁻¹) (1 + x)) =
        ∫ x in (1 + α)..(1 + β), (fun u : ℝ => u⁻¹) x :=
      intervalIntegral.integral_comp_add_left (f := fun u : ℝ => u⁻¹) (a := α) (b := β) 1
    simp only [one_div] at hsub ⊢
    rw [hsub]
    exact integral_inv_of_pos h1α h1β
  by_cases h : α < β
  · have hIco : fundInterval α β = Set.Ico α β := fundInterval_of_lt h
    have h1 : (∫ x in fundInterval α β, 1 / (1 + x)) = ∫ x in α..β, 1 / (1 + x) := by
      rw [hIco, setIntegral_congr_set Ico_ae_eq_Ioc, intervalIntegral.integral_of_le h.le]
    rw [h1, h_int]
    have hle : (1 : ℝ) ≤ (1 + β) / (1 + α) := by
      rw [le_div_iff₀ h1α]
      linarith [h]
    have hnn : (0 : ℝ) ≤ log ((1 + β) / (1 + α)) := Real.log_nonneg hle
    have hb : logb 2 ((1 + β) / (1 + α)) = log ((1 + β) / (1 + α)) / log 2 := rfl
    rw [hb, abs_of_nonneg (div_nonneg hnn hlog2.le)]
  · replace h := le_of_not_gt h
    have hIoc : fundInterval α β = Set.Ioc β α := by simp [fundInterval, not_lt.mpr h]
    have h1 : (∫ x in fundInterval α β, 1 / (1 + x)) = -∫ x in α..β, 1 / (1 + x) := by
      rw [hIoc, intervalIntegral.integral_of_ge h, neg_neg]
    rw [h1, h_int]
    have hpos : (0 : ℝ) ≤ (1 + β) / (1 + α) := div_nonneg h1β.le h1α.le
    have hle : (1 + β) / (1 + α) ≤ 1 := by
      rw [div_le_one h1α]
      linarith [h]
    have hnp : log ((1 + β) / (1 + α)) ≤ 0 := Real.log_nonpos hpos hle
    have hb : logb 2 ((1 + β) / (1 + α)) = log ((1 + β) / (1 + α)) / log 2 := rfl
    rw [hb, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hnp hlog2.le)]
    ring

-- The shifted endpoint stays above `-1` when the sign is even or the numerator is positive.
private theorem one_add_endpoint_pos (P Q S : ℝ) (n : ℕ) (hP0 : 0 ≤ P) (hQ1 : 1 ≤ Q)
    (hS1 : 1 ≤ S) (hPodd : Odd n → 1 ≤ P) :
    (0 : ℝ) < 1 + (P / Q + (-1) ^ n / (Q * S)) := by
  have hQpos : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hSpos : (0 : ℝ) < S := lt_of_lt_of_le zero_lt_one hS1
  have hQS : (1 : ℝ) ≤ Q * S := by nlinarith [hQ1, hS1]
  rcases Nat.even_or_odd n with hev | hod
  · have hp : (-1 : ℝ) ^ n = 1 := hev.neg_one_pow
    rw [hp]
    have h1 : (0 : ℝ) ≤ P / Q := div_nonneg hP0 hQpos.le
    have h2 : (0 : ℝ) < 1 / (Q * S) := by positivity
    linarith
  · have hp : (-1 : ℝ) ^ n = -1 := hod.neg_one_pow
    rw [hp]
    have hP1 := hPodd hod
    have hPQ : (0 : ℝ) < P / Q := div_pos (lt_of_lt_of_le zero_lt_one hP1) hQpos
    have hQSpos : (0 : ℝ) < Q * S := mul_pos hQpos hSpos
    have hle : (1 : ℝ) / (Q * S) ≤ 1 := by
      rw [div_le_one hQSpos]
      exact hQS
    have hneg : (-1 : ℝ) / (Q * S) = -((1 : ℝ) / (Q * S)) := by ring
    rw [hneg]
    linarith

-- The ratio of shifted endpoints equals one plus the determinant offset over the row sums.
private theorem endpoint_ratio (P Q S : ℝ) (n : ℕ) (hQ : Q ≠ 0) (hPQ : P + Q ≠ 0) (hS : S ≠ 0) :
    (1 + (P / Q + (-1) ^ n / (Q * S))) / (1 + P / Q) = 1 + (-1) ^ n / ((P + Q) * S) := by
  have hQS : Q * S ≠ 0 := mul_ne_zero hQ hS
  have h1 : (1 : ℝ) + P / Q = (P + Q) / Q := by
    field_simp
    ring
  rw [h1]
  field_simp
  ring

/-- **Explicit Gauss–Kuzmin mass of a string.** Let $a$ be a string of $n$ positive integers, let
$p$, $q'$ and $q$ be the upper-right, lower-left and lower-right entries of its convergent matrix
$C(a)$, and let $\overleftarrow{a}$ be the reverse of $a$. Then the Gauss–Kuzmin masses satisfy
$P_{GK}(a) = P_{GK}(\overleftarrow{a})$ and
$P_{GK}(a) = \left|\log_2\left(1 + \frac{(-1)^n}{(p + q)(q' + q)}\right)\right|$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 2.5 (`integers-2025-A89-lem-2-5`), equation (2.13). -/
public theorem gaussKuzminMass_eq_abs_logb (a : List ℕ) (ha : (∀ x ∈ a, 0 < x)) :
    gaussKuzminMass a = gaussKuzminMass a.reverse ∧
      gaussKuzminMass a = |logb 2 (1 + (-1) ^ a.length / (((convergentMatrix a 0 1 : ℝ) +
          (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 1 0 : ℝ) +
          (convergentMatrix a 1 1 : ℝ))))| := by
  obtain ⟨-, h01, h10, h11⟩ := cm_entries_nonneg a ha
  have hmass_a : gaussKuzminMass a = |logb 2 (1 + (-1) ^ a.length / (((convergentMatrix a 0 1 : ℝ) +
      (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 1 0 : ℝ) +
      (convergentMatrix a 1 1 : ℝ))))| := by
    unfold gaussKuzminMass
    rw [setIntegral_congr_set (cyl_ae a ha)]
    have hP : (0 : ℝ) ≤ (convergentMatrix a 0 1 : ℝ) := by exact_mod_cast h01
    have hQ1 : (1 : ℝ) ≤ (convergentMatrix a 1 1 : ℝ) := by exact_mod_cast h11
    have h10' : (0 : ℝ) ≤ (convergentMatrix a 1 0 : ℝ) := by exact_mod_cast h10
    have hS1 : (1 : ℝ) ≤ (convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ) := by linarith
    have hPodd : Odd a.length → (1 : ℝ) ≤ (convergentMatrix a 0 1 : ℝ) := by
      intro hod
      have hlen : 0 < a.length := hod.pos
      have hne : a ≠ [] := by
        intro hnil
        rw [hnil] at hlen
        simp at hlen
      exact_mod_cast cm_01_of_ne_nil a ha hne
    have hqpos : (0 : ℝ) < (convergentMatrix a 1 1 : ℝ) := lt_of_lt_of_le zero_lt_one hQ1
    have h1α : (0 : ℝ) < 1 + (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) := by
      have hdiv : (0 : ℝ) ≤ (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) :=
        div_nonneg hP hqpos.le
      linarith
    have h1β : (0 : ℝ) < 1 +
        ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
          ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 1 0 : ℝ) +
            (convergentMatrix a 1 1 : ℝ)))) :=
      one_add_endpoint_pos _ _ _ _ hP hQ1 hS1 hPodd
    rw [fundInterval_integral _ _ h1α h1β]
    have hPQpos : (0 : ℝ) < (convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ) := by
      linarith
    have hSpos : (0 : ℝ) < (convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ) := by
      linarith
    congr 1
    congr 1
    exact endpoint_ratio _ _ _ _ (ne_of_gt hqpos) (ne_of_gt hPQpos) (ne_of_gt hSpos)
  have hmass_r : gaussKuzminMass a.reverse = |logb 2 (1 + (-1) ^ a.length /
      (((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ)) *
      ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ))))| := by
    have hrev := (cfCylinder_reverse_append_cons_ae_eq a ha 1 (le_refl 1)).1
    unfold gaussKuzminMass
    rw [setIntegral_congr_set hrev]
    have hP' : (0 : ℝ) ≤ (convergentMatrix a 1 0 : ℝ) := by exact_mod_cast h10
    have hQ1 : (1 : ℝ) ≤ (convergentMatrix a 1 1 : ℝ) := by exact_mod_cast h11
    have h01' : (0 : ℝ) ≤ (convergentMatrix a 0 1 : ℝ) := by exact_mod_cast h01
    have hS1' : (1 : ℝ) ≤ (convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ) := by linarith
    have hPodd' : Odd a.length → (1 : ℝ) ≤ (convergentMatrix a 1 0 : ℝ) := by
      intro hod
      have hlen : 0 < a.length := hod.pos
      have hne : a ≠ [] := by
        intro hnil
        rw [hnil] at hlen
        simp at hlen
      exact_mod_cast cm_10_of_ne_nil a ha hne
    have hqpos : (0 : ℝ) < (convergentMatrix a 1 1 : ℝ) := lt_of_lt_of_le zero_lt_one hQ1
    have h1α' : (0 : ℝ) < 1 + (convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) := by
      have hdiv : (0 : ℝ) ≤ (convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) :=
        div_nonneg hP' hqpos.le
      linarith
    have h1β' : (0 : ℝ) < 1 +
        ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
          ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
            (convergentMatrix a 1 1 : ℝ)))) :=
      one_add_endpoint_pos _ _ _ _ hP' hQ1 hS1' hPodd'
    rw [fundInterval_integral _ _ h1α' h1β']
    have hPQpos : (0 : ℝ) < (convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ) := by
      linarith
    have hSpos : (0 : ℝ) < (convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ) := by
      linarith
    have hr := endpoint_ratio (convergentMatrix a 1 0 : ℝ) (convergentMatrix a 1 1 : ℝ)
      ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ)) a.length (ne_of_gt hqpos)
      (ne_of_gt hPQpos) (ne_of_gt hSpos)
    congr 1
    congr 1
    rw [hr, mul_comm ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ))
      ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ))]
  exact ⟨hmass_a.trans hmass_r.symm, hmass_a⟩

end

end MetaMathlibExt
