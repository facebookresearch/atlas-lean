/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GaussKuzminSymmetry
import MathlibExt.NumberTheory.GaussKuzminFundamentalIntervals
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.List.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nontrivial symmetries from stable strings

This module proves that the symmetrized extension of a stable string of positive integers is a
nontrivial symmetry: a rearrangement with the same Gauss–Kuzmin mass that differs both from the
string and from its reverse. It also proves that the Gauss–Kuzmin mass of a string of positive
integers equals the mass of its reverse and equals the absolute value of an explicit base-two
logarithm in the entries of its convergent matrix.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 2.5 (`integers-2025-A89-lem-2-5`), equation (2.13), and Lemma 5.7
(`integers-2025-A89-lem-5-7`), equations (5.12) and (5.13).
-/

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory Real

private theorem perm_aux (L : List ℕ) (c : ℕ) :
    (2 :: (c + 1) :: (L.reverse ++ [1])).Perm (2 :: 1 :: (L ++ [c + 1])) := by
  have h1 : (L.reverse ++ [1]).Perm (L ++ [1]) :=
    List.Perm.append_right [1] (List.reverse_perm L)
  have h2 : ((c + 1) :: (L.reverse ++ [1])).Perm ((c + 1) :: (L ++ [1])) :=
    List.Perm.cons (c + 1) h1
  have h3 : ((c + 1) :: (L ++ [1])).Perm (1 :: (L ++ [c + 1])) := by
    have e1 : ((c + 1) :: (L ++ [1])) = ([c + 1] ++ L) ++ [1] := by simp
    rw [e1]
    refine (List.perm_append_comm.trans ?_)
    have e2 : ([1] ++ ([c + 1] ++ L)) = 1 :: ([c + 1] ++ L) := rfl
    rw [e2]
    exact List.Perm.cons 1 List.perm_append_comm
  exact List.Perm.cons 2 (h2.trans h3)

private theorem ne_aux (L : List ℕ) (c : ℕ) (hc : 0 < c) :
    2 :: (c + 1) :: (L.reverse ++ [1]) ≠ 2 :: 1 :: (L ++ [c + 1]) := by
  intro hcon
  have htail := congrArg List.tail hcon
  simp only [List.tail_cons] at htail
  have hhead := congrArg List.head? htail
  simp at hhead
  omega

private theorem ne_rev_aux (L : List ℕ) (c : ℕ) :
    2 :: (c + 1) :: (L.reverse ++ [1]) ≠ (2 :: 1 :: (L ++ [c + 1])).reverse := by
  intro hcon
  have hlast := congrArg List.getLast? hcon
  have eLHS : List.getLast? (2 :: (c + 1) :: (L.reverse ++ [1])) = some 1 := by
    have e : (2 :: (c + 1) :: (L.reverse ++ [1])) = [2, c + 1] ++ (L.reverse ++ [1]) := rfl
    rw [e, List.getLast?_append]
    have h1 : (L.reverse ++ [1]).getLast? = some 1 := by
      rw [List.getLast?_append]
      have hs : ([1].getLast? : Option ℕ) = some 1 := rfl
      rw [hs, Option.some_or]
    rw [h1, Option.some_or]
  have eRHS : List.getLast? (2 :: 1 :: (L ++ [c + 1])).reverse = some 2 := by
    rw [List.getLast?_reverse]
    rfl
  rw [eLHS, eRHS] at hlast
  simp at hlast

private theorem cm_cons_00 (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 0 0 = convergentMatrix a 1 0 := by
  rw [convergentMatrix_cons]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cm_cons_01 (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 0 1 = convergentMatrix a 1 1 := by
  rw [convergentMatrix_cons]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cm_cons_10 (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 1 0 =
      convergentMatrix a 0 0 + t * convergentMatrix a 1 0 := by
  rw [convergentMatrix_cons]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cm_cons_11 (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 1 1 =
      convergentMatrix a 0 1 + t * convergentMatrix a 1 1 := by
  rw [convergentMatrix_cons]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cm_append (l₁ l₂ : List ℕ) :
    convergentMatrix (l₁ ++ l₂) = convergentMatrix l₁ * convergentMatrix l₂ := by
  simp [convergentMatrix, List.map_append, List.prod_append]

private theorem cm_append_00 (l : List ℕ) (s : ℕ) :
    convergentMatrix (l ++ [s]) 0 0 = convergentMatrix l 0 1 := by
  rw [cm_append]
  have : convergentMatrix [s] = !![0, 1; 1, (s : ℤ)] := by
    simp [convergentMatrix_cons, convergentMatrix_nil]
  rw [this]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cm_append_01 (l : List ℕ) (s : ℕ) :
    convergentMatrix (l ++ [s]) 0 1 =
      convergentMatrix l 0 0 + s * convergentMatrix l 0 1 := by
  rw [cm_append]
  have : convergentMatrix [s] = !![0, 1; 1, (s : ℤ)] := by
    simp [convergentMatrix_cons, convergentMatrix_nil]
  rw [this]
  simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem cm_append_10 (l : List ℕ) (s : ℕ) :
    convergentMatrix (l ++ [s]) 1 0 = convergentMatrix l 1 1 := by
  rw [cm_append]
  have : convergentMatrix [s] = !![0, 1; 1, (s : ℤ)] := by
    simp [convergentMatrix_cons, convergentMatrix_nil]
  rw [this]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cm_append_11 (l : List ℕ) (s : ℕ) :
    convergentMatrix (l ++ [s]) 1 1 =
      convergentMatrix l 1 0 + s * convergentMatrix l 1 1 := by
  rw [cm_append]
  have : convergentMatrix [s] = !![0, 1; 1, (s : ℤ)] := by
    simp [convergentMatrix_cons, convergentMatrix_nil]
  rw [this]
  simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem entries_nonneg (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    0 ≤ convergentMatrix a 0 0 ∧ 0 ≤ convergentMatrix a 0 1 ∧
    0 ≤ convergentMatrix a 1 0 ∧ 1 ≤ convergentMatrix a 1 1 := by
  induction a with
  | nil => simp [convergentMatrix_nil]
  | cons t a ih =>
    have ht : 0 < t := ha t (by simp)
    have ha' : ∀ x ∈ a, 0 < x := fun x hx => ha x (by simp [hx])
    obtain ⟨h00, h01, h10, h11⟩ := ih ha'
    have ht0 : (0 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht.le
    have ht1 : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
    rw [cm_cons_00, cm_cons_01, cm_cons_10, cm_cons_11]
    refine ⟨h10, by omega, ?_, ?_⟩
    · have hmul : (0 : ℤ) ≤ (t : ℤ) * convergentMatrix a 1 0 := by positivity
      linarith
    · have hmul : (1 : ℤ) * 1 ≤ (t : ℤ) * convergentMatrix a 1 1 :=
        mul_le_mul ht1 h11 zero_le_one ht0
      rw [mul_one] at hmul
      linarith

private theorem integral_fundInterval (α β : ℝ) (hα : -1 < α) (hβ : -1 < β) :
    ∫ x in fundInterval α β, 1 / (1 + x) = |Real.log (1 + β) - Real.log (1 + α)| := by
  have hFTC : ∀ u v : ℝ, -1 < u → -1 < v →
      (∫ x in u..v, 1 / (1 + x)) = Real.log (1 + v) - Real.log (1 + u) := by
    intro u v hu hv
    have hmem : ∀ x ∈ Set.uIcc u v, (-1 : ℝ) < x := by
      intro x hx
      have hxlo : min u v ≤ x := by
        rcases le_total u v with h | h
        · rw [Set.uIcc_of_le h] at hx
          rw [min_eq_left h]
          exact hx.1
        · rw [Set.uIcc_of_ge h] at hx
          rw [min_eq_right h]
          exact hx.1
      exact lt_of_lt_of_le (lt_min hu hv) hxlo
    have hderiv : ∀ x ∈ Set.uIcc u v,
        HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + x)) x := by
      intro x hx
      have hne : (1 : ℝ) + x ≠ 0 := by have := hmem x hx; linarith
      have hid : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id x).const_add 1
      exact hid.log hne
    have hcont : ContinuousOn (fun x : ℝ => 1 / (1 + x)) (Set.uIcc u v) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_id.const_add 1)
      intro x hx
      have := hmem x hx
      change (1 : ℝ) + x ≠ 0
      linarith
    have hint : IntervalIntegrable (fun x : ℝ => 1 / (1 + x)) volume u v :=
      hcont.intervalIntegrable
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  by_cases hlt : α < β
  · rw [fundInterval_of_lt hlt, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (le_of_lt hlt), hFTC α β hα hβ]
    have hle : Real.log (1 + α) ≤ Real.log (1 + β) := by
      rw [Real.log_le_log_iff (by linarith) (by linarith)]
      linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  · have hle : β ≤ α := le_of_not_gt hlt
    have hfund : fundInterval α β = Set.Ioc β α := by
      unfold fundInterval
      exact ite_eq_right (not_lt.mpr hle)
    rw [hfund, ← intervalIntegral.integral_of_le hle, hFTC β α hβ hα]
    have hle' : Real.log (1 + β) ≤ Real.log (1 + α) := by
      rw [Real.log_le_log_iff (by linarith) (by linarith)]
      linarith
    rw [show Real.log (1 + α) - Real.log (1 + β) =
      -(Real.log (1 + β) - Real.log (1 + α)) by ring,
      abs_of_nonpos (sub_nonpos.mpr hle')]

private theorem mass_cons_formula (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) (t : ℕ)
    (ht : 1 ≤ t) :
    gaussKuzminMass (t :: a) =
      |Real.logb 2 (1 + (-1 : ℝ) ^ (t :: a).length /
        ((characteristicNumber (t :: a) : ℤ) : ℝ))| := by
  have h3 := (cfCylinder_reverse_append_cons_ae_eq a ha t ht).2.2.1
  set p' : ℝ := ((convergentMatrix a 0 0 : ℤ) : ℝ) with hp'def
  set p : ℝ := ((convergentMatrix a 0 1 : ℤ) : ℝ) with hpdef
  set q' : ℝ := ((convergentMatrix a 1 0 : ℤ) : ℝ) with hq'def
  set q : ℝ := ((convergentMatrix a 1 1 : ℤ) : ℝ) with hqdef
  set T : ℝ := ((t : ℕ) : ℝ) with hTdef
  set D1 : ℝ := p + T * q with hD1def
  set D2 : ℝ := p' + p + T * (q' + q) with hD2def
  set s : ℝ := (-1 : ℝ) ^ (a.length + 1) with hsdef
  set α : ℝ := q / D1 with hαdef
  set β : ℝ := α + s / (D1 * D2) with hβdef
  obtain ⟨hp'nn, hpnn, hq'nn, hq1⟩ := entries_nonneg a ha
  have hp'R : (0 : ℝ) ≤ p' := by rw [hp'def]; exact_mod_cast hp'nn
  have hpR : (0 : ℝ) ≤ p := by rw [hpdef]; exact_mod_cast hpnn
  have hq'R : (0 : ℝ) ≤ q' := by rw [hq'def]; exact_mod_cast hq'nn
  have hqR : (1 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast hq1
  have hTR : (1 : ℝ) ≤ T := by rw [hTdef]; exact_mod_cast ht
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hD1 : (1 : ℝ) ≤ D1 := by
    rw [hD1def]
    have hTq : (1 : ℝ) ≤ T * q := by
      have h := mul_le_mul hTR hqR zero_le_one hT0
      rwa [mul_one] at h
    linarith
  have hD2 : (1 : ℝ) ≤ D2 := by
    rw [hD2def]
    have hTqq : (1 : ℝ) ≤ T * (q' + q) := by
      have hqq : (1 : ℝ) ≤ q' + q := by linarith
      have h := mul_le_mul hTR hqq zero_le_one hT0
      rwa [mul_one] at h
    linarith
  have hαnn : (0 : ℝ) ≤ α := by
    rw [hαdef]
    exact div_nonneg hq0 (by linarith)
  have hs2 : s ^ 2 = 1 := by
    have hev : Even ((a.length + 1) + (a.length + 1)) := ⟨a.length + 1, by ring⟩
    have h2 : (-1 : ℝ) ^ ((a.length + 1) + (a.length + 1)) = 1 := Even.neg_one_pow hev
    rw [hsdef, sq, ← pow_add]
    exact h2
  have hslo : (-1 : ℝ) ≤ s := by
    have h := sq_nonneg (s + 1)
    rw [add_sq, mul_one, one_pow] at h
    linarith [hs2]
  have hD1ne : D1 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < D1)
  have hD2ne : D2 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < D2)
  have hβeq : β = (q * D2 + s) / (D1 * D2) := by
    rw [hβdef, hαdef]
    field_simp
  have hβnn : (0 : ℝ) ≤ β := by
    rw [hβeq]
    have hqD2 : (1 : ℝ) ≤ q * D2 := by
      have h := mul_le_mul hqR hD2 zero_le_one hq0
      rwa [mul_one] at h
    have hnum : (0 : ℝ) ≤ q * D2 + s := by linarith
    have hden : (0 : ℝ) < D1 * D2 := mul_pos (by linarith) (by linarith)
    exact div_nonneg hnum hden.le
  have hα' : (-1 : ℝ) < α := by linarith
  have hβ' : (-1 : ℝ) < β := by linarith
  have h1α : (0 : ℝ) < 1 + α := by linarith
  have h1β : (0 : ℝ) < 1 + β := by linarith
  have hχ : ((characteristicNumber (t :: a) : ℤ) : ℝ) = (D1 + q) * D2 := by
    simp only [characteristicNumber, cm_cons_01, cm_cons_11, cm_cons_10]
    push_cast
    rw [hD1def, hD2def, hpdef, hp'def, hqdef, hq'def, hTdef]
    ring
  have hratio : (1 + β) / (1 + α) =
      1 + s / ((characteristicNumber (t :: a) : ℤ) : ℝ) := by
    rw [hχ, hβdef, hαdef]
    have hD1q : D1 + q ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < D1 + q)
    have hqD1nn : (0 : ℝ) ≤ q / D1 := div_nonneg hq0 (by linarith)
    have hdenα : (1 : ℝ) + q / D1 ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have e1 : Real.log (1 + β) - Real.log (1 + α) = Real.log ((1 + β) / (1 + α)) := by
    rw [Real.log_div h1β.ne' h1α.ne']
  simp only [gaussKuzminMass]
  rw [MeasureTheory.setIntegral_congr_set h3, integral_fundInterval α β hα' hβ', e1,
    hratio, List.length_cons, ← hsdef]
  change |Real.log _| / Real.log 2 = |Real.log _ / Real.log 2|
  rw [abs_div, abs_of_pos hlog2]

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
  have hformula : ∀ b : List ℕ, (∀ x ∈ b, 0 < x) → gaussKuzminMass b =
      |Real.logb 2 (1 + (-1 : ℝ) ^ b.length / ((characteristicNumber b : ℤ) : ℝ))| := by
    intro b hb
    cases b with
    | nil =>
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
      rw [gaussKuzminMass_nil, ← fundInterval_of_lt (zero_lt_one : (0 : ℝ) < 1),
        integral_fundInterval 0 1 (by norm_num) (by norm_num), characteristicNumber_nil]
      norm_num
      rw [abs_of_pos hlog2, div_self hlog2.ne']
    | cons t b =>
      exact mass_cons_formula b (fun x hx => hb x (List.mem_cons_of_mem t hx)) t
        (hb t List.mem_cons_self)
  have hrev := (convergentMatrix_reverse_append_cons a ha 1 le_rfl).1
  have e01 : convergentMatrix a.reverse 0 1 = convergentMatrix a 1 0 := by rw [hrev]; simp
  have e10 : convergentMatrix a.reverse 1 0 = convergentMatrix a 0 1 := by rw [hrev]; simp
  have e11 : convergentMatrix a.reverse 1 1 = convergentMatrix a 1 1 := by rw [hrev]; simp
  have hχ : characteristicNumber a.reverse = characteristicNumber a := by
    simp only [characteristicNumber, e01, e10, e11]
    ring
  have hχR : ((characteristicNumber a : ℤ) : ℝ) = ((convergentMatrix a 0 1 : ℝ) +
      (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 1 0 : ℝ) +
      (convergentMatrix a 1 1 : ℝ)) := by
    simp only [characteristicNumber]
    push_cast
    ring
  have hrpos : ∀ x ∈ a.reverse, 0 < x := fun x hx => ha x (List.mem_reverse.mp hx)
  refine ⟨?_, ?_⟩
  · rw [hformula a ha, hformula a.reverse hrpos, List.length_reverse, hχ]
  · rw [hformula a ha, hχR]

private theorem mass_aux (L : List ℕ) (c : ℕ) (hc : 0 < c) (hL : ∀ x ∈ L, 0 < x)
    (hstL : convergentMatrix (L ++ [c]) 0 1 = 2 * convergentMatrix (L ++ [c]) 1 0) :
    gaussKuzminMass (2 :: (c + 1) :: (L.reverse ++ [1])) =
      gaussKuzminMass (2 :: 1 :: (L ++ [c + 1])) := by
  have hc1 : 1 ≤ c := hc
  have hLstab : convergentMatrix L 0 0 + c * convergentMatrix L 0 1 =
      2 * convergentMatrix L 1 1 := by
    simpa [cm_append_01, cm_append_10] using hstL
  have hrev := (convergentMatrix_reverse_append_cons L hL c hc1).1
  have er00 : convergentMatrix L.reverse 0 0 = convergentMatrix L 0 0 := by
    rw [hrev]; simp
  have er01 : convergentMatrix L.reverse 0 1 = convergentMatrix L 1 0 := by
    rw [hrev]; simp
  have er10 : convergentMatrix L.reverse 1 0 = convergentMatrix L 0 1 := by
    rw [hrev]; simp
  have er11 : convergentMatrix L.reverse 1 1 = convergentMatrix L 1 1 := by
    rw [hrev]; simp
  have cross1 : convergentMatrix (2 :: 1 :: (L ++ [c + 1])) 0 1 +
      convergentMatrix (2 :: 1 :: (L ++ [c + 1])) 1 1 =
      convergentMatrix (2 :: (c + 1) :: (L.reverse ++ [1])) 1 0 +
      convergentMatrix (2 :: (c + 1) :: (L.reverse ++ [1])) 1 1 := by
    simp only [cm_cons_00, cm_cons_01, cm_cons_10, cm_cons_11, cm_append_00,
      cm_append_01, cm_append_10, cm_append_11, er00, er01, er10, er11,
      Nat.cast_add, Nat.cast_one]
    linear_combination hLstab
  have cross2 : convergentMatrix (2 :: 1 :: (L ++ [c + 1])) 1 0 +
      convergentMatrix (2 :: 1 :: (L ++ [c + 1])) 1 1 =
      convergentMatrix (2 :: (c + 1) :: (L.reverse ++ [1])) 0 1 +
      convergentMatrix (2 :: (c + 1) :: (L.reverse ++ [1])) 1 1 := by
    simp only [cm_cons_00, cm_cons_01, cm_cons_10, cm_cons_11, cm_append_00,
      cm_append_01, cm_append_10, cm_append_11, er00, er01, er10, er11,
      Nat.cast_add, Nat.cast_one]
    linear_combination -hLstab
  have hχeq : characteristicNumber (2 :: 1 :: (L ++ [c + 1])) =
      characteristicNumber (2 :: (c + 1) :: (L.reverse ++ [1])) := by
    simp only [characteristicNumber]
    rw [cross1, cross2]
    ring
  have hlen : (2 :: (c + 1) :: (L.reverse ++ [1])).length =
      (2 :: 1 :: (L ++ [c + 1])).length := by
    simp [List.length_reverse]
  have hapos : ∀ x ∈ (1 :: (L ++ [c + 1])), 0 < x := by
    intro x hx
    rw [List.mem_cons, List.mem_append, List.mem_singleton] at hx
    rcases hx with rfl | hx | rfl
    · exact one_pos
    · exact hL x hx
    · omega
  have hsgpos : ∀ x ∈ ((c + 1) :: (L.reverse ++ [1])), 0 < x := by
    intro x hx
    rw [List.mem_cons, List.mem_append, List.mem_singleton, List.mem_reverse] at hx
    rcases hx with rfl | hx | rfl
    · omega
    · exact hL x hx
    · exact one_pos
  have hap := mass_cons_formula (1 :: (L ++ [c + 1])) hapos 2 one_le_two
  have hsg := mass_cons_formula ((c + 1) :: (L.reverse ++ [1])) hsgpos 2 one_le_two
  rw [hsg, hap, hlen, ← hχeq]

/-- **Nontrivial symmetries from stable strings.** Let $n \ge 1$ and let $a = (a_1, \dots, a_n)$ be
a stable string of positive integers. Put $a^+ = (2, 1, a_1, \dots, a_{n-1}, a_n + 1)$ and
$\sigma(a^+) = (2, a_n + 1, a_{n-1}, \dots, a_1, 1)$. Then $\sigma(a^+)$ is a rearrangement of
$a^+$, it differs both from $a^+$ and from the reverse of $a^+$, and
$P_{GK}(\sigma(a^+)) = P_{GK}(a^+)$, where $P_{GK}$ denotes the Gauss–Kuzmin measure of a string.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.7 (`integers-2025-A89-lem-5-7`), equations (5.12) and (5.13). -/
public theorem stable_plus_nontrivial_symmetry (a : List ℕ) (ha : (∀ x ∈ a, 0 < x)) (h : a ≠
    [])
    (hst : IsStableString a) :
    let ap := 2 :: 1 :: (a.dropLast ++ [a.getLast h + 1])
    let sg := 2 :: (a.getLast h + 1) :: (a.dropLast.reverse ++ [1])
    sg.Perm ap ∧ sg ≠ ap ∧ sg ≠ ap.reverse ∧ gaussKuzminMass sg = gaussKuzminMass ap := by
  have ha_eq : a = a.dropLast ++ [a.getLast h] := (List.dropLast_append_getLast h).symm
  have hc : 0 < a.getLast h := ha _ (List.getLast_mem h)
  have hL : ∀ x ∈ a.dropLast, 0 < x := by
    intro x hx
    apply ha
    rw [ha_eq]
    exact List.mem_append_left [a.getLast h] hx
  have hstL : convergentMatrix (a.dropLast ++ [a.getLast h]) 0 1 =
      2 * convergentMatrix (a.dropLast ++ [a.getLast h]) 1 0 := by
    rw [← ha_eq]
    exact hst
  exact ⟨perm_aux _ _, ne_aux _ _ hc, ne_rev_aux _ _, mass_aux _ _ hc hL hstL⟩

end

end MetaMathlibExt
