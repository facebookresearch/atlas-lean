/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.NumberTheory.GaussKuzminSymmetry
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Piecewise
import MathlibExt.NumberTheory.GaussKuzminFundamentalIntervals

/-!
# Symmetry up to a fixed length does not force the Gauss–Kuzmin density

This module proves that for every integer `N ≥ 1` there is a continuous probability density on
`[0, 1]`, distinct from the Gauss–Kuzmin density, whose integrals over fundamental intervals are
reversal-symmetric for all strings of length at most `N`.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Theorem 2 (`integers-2025-A89-thm-2`).
-/

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory Filter Topology Real

/-- The continued fraction digit sequence is unchanged by taking fractional parts. -/
private theorem s_eq_of_fract (w : ℝ) :
    (GenContFract.of w).s = (GenContFract.of (Int.fract w)).s := by
  by_cases h : Int.fract w = 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, w = a := ⟨⌊w⌋, by
      have h' := Int.floor_add_fract w
      rw [h] at h'
      simpa using h'.symm⟩
    rw [Int.fract_intCast]
    have h0 : (GenContFract.of (0 : ℝ)).s = Stream'.Seq.nil := by
      simpa using GenContFract.of_s_of_int (K := ℝ) (0 : ℤ)
    simp [GenContFract.of_s_of_int, h0]
  · apply Stream'.Seq.ext
    intro n
    cases n with
    | zero =>
      have h1 := GenContFract.of_s_head (K := ℝ) (v := w) h
      have h2 := GenContFract.of_s_head (K := ℝ) (v := Int.fract w) (by simp [h, Int.fract_fract])
      simp only [Int.fract_fract] at h2
      have e0 : ∀ s : Stream'.Seq (GenContFract.Pair ℝ), s.get? 0 = s.head := fun s => rfl
      rw [e0, e0, h1, h2]
    | succ n =>
      rw [GenContFract.of_s_succ, GenContFract.of_s_succ]
      simp only [Int.fract_fract]

/-- Partial denominators are unchanged by taking fractional parts. -/
private theorem partDens_eq_of_fract (w : ℝ) (i : ℕ) :
    (GenContFract.of w).partDens.get? i = (GenContFract.of (Int.fract w)).partDens.get? i := by
  change (Stream'.Seq.map GenContFract.Pair.b (GenContFract.of w).s).get? i =
    (Stream'.Seq.map GenContFract.Pair.b (GenContFract.of (Int.fract w)).s).get? i
  rw [Stream'.Seq.map_get?, Stream'.Seq.map_get?, s_eq_of_fract]

/-- Shifting past the first partial denominator. -/
private theorem partDens_succ (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (i : ℕ) :
    (GenContFract.of x).partDens.get? (i + 1) =
      (GenContFract.of x⁻¹).partDens.get? i := by
  have hfr : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx0.le, hx1⟩
  have h1 : (GenContFract.of x).partDens.get? (i + 1) =
      (GenContFract.of (Int.fract x)⁻¹).partDens.get? i := by
    simp only [GenContFract.partDens, Stream'.Seq.map_get?, GenContFract.of_s_succ]
  rw [hfr] at h1
  exact h1

/-- The first partial denominator of a number in `(0, 1)`. -/
private theorem partDens_zero (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (GenContFract.of x).partDens.get? 0 = some ((⌊x⁻¹⌋ : ℤ) : ℝ) := by
  have hfr : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx0.le, hx1⟩
  have hs : (GenContFract.of x).s.get? 0 = some ⟨1, ((⌊x⁻¹⌋ : ℤ) : ℝ)⟩ := by
    have h1 := GenContFract.of_s_head (K := ℝ) (v := x) (by rw [hfr]; exact ne_of_gt hx0)
    rw [hfr] at h1
    exact h1
  change (Stream'.Seq.map GenContFract.Pair.b (GenContFract.of x).s).get? 0 = _
  rw [Stream'.Seq.map_get?, hs]
  rfl

/-- Every all-ones cylinder contains a nonempty open interval strictly inside `(0, 1)`. -/
private theorem exists_Ioo_subset_cfCylinder_replicate (k : ℕ) :
    ∃ α β : ℝ, 0 < α ∧ α < β ∧ β < 1 ∧
      Set.Ioo α β ⊆ cfCylinder (List.replicate k 1) := by
  induction k with
  | zero =>
    refine ⟨1 / 3, 2 / 3, by norm_num, by norm_num, by norm_num, ?_⟩
    intro x hx
    rw [List.replicate_zero, cfCylinder_nil]
    obtain ⟨hx1, hx2⟩ := hx
    norm_num at hx1 hx2 ⊢
    exact ⟨by linarith, by linarith⟩
  | succ k ih =>
    obtain ⟨α, β, hα, hαβ, hβ1, hsub⟩ := ih
    have hβ0 : 0 < β := lt_trans hα hαβ
    have hA0 : (0 : ℝ) < 1 + α := by linarith
    have hB0 : (0 : ℝ) < 1 + β := by linarith
    have hα'β' : (1 : ℝ) / (1 + β) < 1 / (1 + α) :=
      one_div_lt_one_div_of_lt hA0 (by linarith)
    have hβ'1 : (1 : ℝ) / (1 + α) < 1 := by
      rw [div_lt_one hA0]
      linarith
    refine ⟨1 / (1 + β), 1 / (1 + α), by positivity, hα'β', hβ'1, ?_⟩
    intro x hx
    obtain ⟨hxlow, hxhigh⟩ := hx
    have hx0 : 0 < x := lt_trans (by positivity) hxlow
    have hx1 : x < 1 := lt_trans hxhigh hβ'1
    have hA1 : (0 : ℝ) < 1 / (1 + α) := by positivity
    have hB1 : (0 : ℝ) < 1 / (1 + β) := by positivity
    have hlower : (1 : ℝ) + α < x⁻¹ := by
      have h := (inv_lt_inv₀ hA1 hx0).mpr hxhigh
      rwa [one_div, inv_inv] at h
    have hupper : x⁻¹ < (1 : ℝ) + β := by
      have h := (inv_lt_inv₀ hx0 hB1).mpr hxlow
      rwa [one_div, inv_inv] at h
    have hfloor : ⌊x⁻¹⌋ = (1 : ℤ) := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    have hfr : Int.fract x⁻¹ = x⁻¹ - 1 := by
      rw [Int.fract, hfloor]
      push_cast
      ring
    have hy : Int.fract x⁻¹ ∈ Set.Ioo α β := by
      rw [hfr]
      constructor <;> linarith
    have hycyl := hsub hy
    rw [List.replicate_succ]
    refine ⟨⟨hx0.le, hx1⟩, fun j hj => ?_⟩
    cases j with
    | zero =>
      have h0 := partDens_zero x hx0 hx1
      rw [hfloor] at h0
      simpa using h0
    | succ i =>
      have hi : i < (List.replicate k 1).length := by
        have hlen : (1 :: List.replicate k 1).length = (List.replicate k 1).length + 1 := rfl
        omega
      have h1 := partDens_succ x hx0 hx1 i
      have h2 := partDens_eq_of_fract x⁻¹ i
      rw [h1, h2]
      have h3 := hycyl.2 i hi
      simpa [List.getElem_cons_succ] using h3

/-- Entry formulas for prepending a digit. -/
private theorem cm_cons_00 (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 0 0 = convergentMatrix a 1 0 := by
  rw [convergentMatrix_cons]; simp [Matrix.mul_apply, Fin.sum_univ_two]
private theorem cm_cons_01 (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 0 1 = convergentMatrix a 1 1 := by
  rw [convergentMatrix_cons]; simp [Matrix.mul_apply, Fin.sum_univ_two]
private theorem cm_cons_10 (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 1 0 = convergentMatrix a 0 0 + t * convergentMatrix a 1 0 := by
  rw [convergentMatrix_cons]; simp [Matrix.mul_apply, Fin.sum_univ_two]
private theorem cm_cons_11 (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) 1 1 = convergentMatrix a 0 1 + t * convergentMatrix a 1 1 := by
  rw [convergentMatrix_cons]; simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Entry bounds for the convergent matrix of a nonempty positive string. -/
private theorem entries_of_pos_ne_nil (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) (hne : a ≠ []) :
    0 ≤ convergentMatrix a 0 0 ∧ convergentMatrix a 0 0 ≤ convergentMatrix a 0 1 ∧
    0 ≤ convergentMatrix a 0 1 ∧ convergentMatrix a 0 1 ≤ convergentMatrix a 1 1 ∧
    1 ≤ convergentMatrix a 0 1 ∧ 0 ≤ convergentMatrix a 1 0 ∧
    convergentMatrix a 1 0 ≤ convergentMatrix a 1 1 ∧ 1 ≤ convergentMatrix a 1 0 ∧
    1 ≤ convergentMatrix a 1 1 := by
  induction a with
  | nil => exact absurd rfl hne
  | cons t b ih =>
    cases b with
    | nil =>
      have ht : 0 < t := ha t (by simp)
      have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast ht
      have e00 : convergentMatrix [t] 0 0 = 0 := by
        rw [cm_cons_00, convergentMatrix_nil]
        exact Matrix.one_apply_ne (by decide)
      have e01 : convergentMatrix [t] 0 1 = 1 := by
        rw [cm_cons_01, convergentMatrix_nil]
        exact Matrix.one_apply_eq 1
      have e10 : convergentMatrix [t] 1 0 = 1 := by
        rw [cm_cons_10, convergentMatrix_nil, Matrix.one_apply_eq,
          Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
        ring
      have e11 : convergentMatrix [t] 1 1 = t := by
        rw [cm_cons_11, convergentMatrix_nil, Matrix.one_apply_eq,
          Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
        ring
      refine ⟨by rw [e00], by rw [e00, e01]; exact zero_le_one, by rw [e01]; exact zero_le_one,
        by rw [e01, e11]; exact ht1, by rw [e01], by rw [e10]; exact zero_le_one,
        by rw [e10, e11]; exact ht1, by rw [e10], by rw [e11]; exact ht1⟩
    | cons t' b' =>
      have ht : 0 < t := ha t (by simp)
      have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast ht
      have ht0 : (0 : ℤ) ≤ t := by exact_mod_cast Nat.zero_le t
      have ha' : ∀ x ∈ t' :: b', 0 < x := fun x hx => ha x (by simp [hx])
      obtain ⟨h00, h0001, h01, h0111, h01ge, h10, h1011, h10ge, h11⟩ :=
        ih ha' (by simp)
      rw [cm_cons_00 t (t' :: b'), cm_cons_01 t (t' :: b'), cm_cons_10 t (t' :: b'),
        cm_cons_11 t (t' :: b')]
      have hge11 : convergentMatrix (t' :: b') 1 1 ≤
          (t : ℤ) * convergentMatrix (t' :: b') 1 1 :=
        le_mul_of_one_le_left (by omega) ht1
      have hmul10 : (1 : ℤ) ≤ t * convergentMatrix (t' :: b') 1 0 := by
        calc (1 : ℤ) = 1 * 1 := by ring
          _ ≤ t * convergentMatrix (t' :: b') 1 0 :=
            mul_le_mul ht1 h10ge (by norm_num) (by linarith)
      have hmul11 : (1 : ℤ) ≤ t * convergentMatrix (t' :: b') 1 1 := by
        calc (1 : ℤ) = 1 * 1 := by ring
          _ ≤ t * convergentMatrix (t' :: b') 1 1 :=
            mul_le_mul ht1 h11 (by norm_num) (by linarith)
      refine ⟨h10, h1011, by omega, by linarith, h11, by positivity,
        add_le_add h0001 (mul_le_mul_of_nonneg_left h1011 ht0), by linarith, by linarith⟩

/-- The reversed cylinder is almost everywhere an explicit interval. -/
private theorem ae_eq_fundInterval_of_reverse (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    cfCylinder a.reverse =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ))
          ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
              ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
              (convergentMatrix a 1 1 : ℝ)))) :=
  (cfCylinder_reverse_append_cons_ae_eq a ha 1 le_rfl).1

/-- A cylinder is almost everywhere an explicit interval. -/
private theorem ae_eq_fundInterval_of_self (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    cfCylinder a =ᵐ[volume]
        fundInterval ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ))
          ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
              ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 1 0 : ℝ) +
              (convergentMatrix a 1 1 : ℝ)))) := by
  have ha_rev : ∀ x ∈ a.reverse, 0 < x := by
    intro x hx
    rw [List.mem_reverse] at hx
    exact ha x hx
  have h := (cfCylinder_reverse_append_cons_ae_eq a.reverse ha_rev 1 le_rfl).1
  rw [List.reverse_reverse, List.length_reverse] at h
  have hm1 := (convergentMatrix_reverse_append_cons a ha 1 le_rfl).1
  have e10 : convergentMatrix a.reverse 1 0 = convergentMatrix a 0 1 := by rw [hm1]; simp
  have e11 : convergentMatrix a.reverse 1 1 = convergentMatrix a 1 1 := by rw [hm1]; simp
  have e01 : convergentMatrix a.reverse 0 1 = convergentMatrix a 1 0 := by rw [hm1]; simp
  rw [e10, e11, e01] at h
  exact h

/-- The interval endpoints of a nonempty positive string lie in `[0, 2]`. -/
private theorem fundInterval_endpoints_mem (a : List ℕ) (ha : ∀ x ∈ a, 0 < x)
    (hne : a ≠ []) :
    0 ≤ ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ)) ∧
    ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ)) ≤ 1 ∧
    0 ≤ ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
      ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
        (convergentMatrix a 1 1 : ℝ)))) ∧
    ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
      ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
        (convergentMatrix a 1 1 : ℝ)))) ≤ 2 ∧
    0 ≤ ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)) ∧
    ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)) ≤ 1 ∧
    0 ≤ ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
      ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 1 0 : ℝ) +
        (convergentMatrix a 1 1 : ℝ)))) ∧
    ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
      ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 1 0 : ℝ) +
        (convergentMatrix a 1 1 : ℝ)))) ≤ 2 := by
  obtain ⟨h00, h0001, h01, h0111, h01ge, h10, h1011, h10ge, h11⟩ :=
    entries_of_pos_ne_nil a ha hne
  have hP : (0 : ℝ) ≤ (convergentMatrix a 0 1 : ℝ) := by exact_mod_cast h01
  have hR : (0 : ℝ) ≤ (convergentMatrix a 1 0 : ℝ) := by exact_mod_cast h10
  have hQ : (0 : ℝ) < (convergentMatrix a 1 1 : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one h11
  have hQ1 : (1 : ℝ) ≤ (convergentMatrix a 1 1 : ℝ) := by exact_mod_cast h11
  have hP1 : (1 : ℝ) ≤ (convergentMatrix a 0 1 : ℝ) := by exact_mod_cast h01ge
  have hR1 : (1 : ℝ) ≤ (convergentMatrix a 1 0 : ℝ) := by exact_mod_cast h10ge
  have hPQle : (convergentMatrix a 0 1 : ℝ) ≤ (convergentMatrix a 1 1 : ℝ) := by
    exact_mod_cast h0111
  have hRQle : (convergentMatrix a 1 0 : ℝ) ≤ (convergentMatrix a 1 1 : ℝ) := by
    exact_mod_cast h1011
  have hPQ : (0 : ℝ) < (convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ) := by
    linarith
  have hRQ : (0 : ℝ) < (convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ) := by
    linarith
  have hPQ1 : (1 : ℝ) ≤ (convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ) := by
    linarith
  have hRQ1 : (1 : ℝ) ≤ (convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ) := by
    linarith
  have hD1 : (0 : ℝ) < (convergentMatrix a 1 1 : ℝ) *
      ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ)) := mul_pos hQ hPQ
  have hD2 : (0 : ℝ) < (convergentMatrix a 1 1 : ℝ) *
      ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ)) := mul_pos hQ hRQ
  have hD1ge : (1 : ℝ) ≤ (convergentMatrix a 1 1 : ℝ) *
      ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ)) := by nlinarith
  have hD2ge : (1 : ℝ) ≤ (convergentMatrix a 1 1 : ℝ) *
      ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ)) := by nlinarith
  have hα1 : 0 ≤ (convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) :=
    div_nonneg hR hQ.le
  have hα1le : (convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) ≤ 1 := by
    rw [div_le_one hQ]
    exact hRQle
  have hα2 : 0 ≤ (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) :=
    div_nonneg hP hQ.le
  have hα2le : (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) ≤ 1 := by
    rw [div_le_one hQ]
    exact hPQle
  have hsign : (-1 : ℝ) ^ a.length = 1 ∨ (-1 : ℝ) ^ a.length = -1 := by
    rcases Nat.even_or_odd a.length with he | ho
    · exact Or.inl (Even.neg_one_pow he)
    · exact Or.inr (Odd.neg_one_pow ho)
  refine ⟨hα1, hα1le, ?_, ?_, hα2, hα2le, ?_, ?_⟩
  · rcases hsign with hs | hs
    · rw [hs]
      have hpos : (0 : ℝ) ≤ 1 / ((convergentMatrix a 1 1 : ℝ) *
          ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ))) :=
        div_nonneg zero_le_one hD1.le
      linarith
    · rw [hs]
      have hRP : (1 : ℝ) ≤ (convergentMatrix a 1 0 : ℝ) *
          ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ)) := by nlinarith
      have heq : (convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) +
          -1 / ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ))) =
          ((convergentMatrix a 1 0 : ℝ) *
            ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ)) - 1) /
          ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ))) := by
        field_simp
        ring
      rw [heq]
      exact div_nonneg (by linarith) hD1.le
  · rcases hsign with hs | hs
    · rw [hs]
      have hle : (1 : ℝ) / ((convergentMatrix a 1 1 : ℝ) *
          ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ))) ≤ 1 := by
        rw [div_le_one hD1]
        exact hD1ge
      linarith
    · rw [hs]
      have hneg : (-1 : ℝ) / ((convergentMatrix a 1 1 : ℝ) *
          ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ))) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by norm_num) hD1.le
      linarith
  · rcases hsign with hs | hs
    · rw [hs]
      have hpos : (0 : ℝ) ≤ 1 / ((convergentMatrix a 1 1 : ℝ) *
          ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ))) :=
        div_nonneg zero_le_one hD2.le
      linarith
    · rw [hs]
      have hPR : (1 : ℝ) ≤ (convergentMatrix a 0 1 : ℝ) *
          ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ)) := by nlinarith
      have heq : (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) +
          -1 / ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ))) =
          ((convergentMatrix a 0 1 : ℝ) *
            ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ)) - 1) /
          ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ))) := by
        field_simp
        ring
      rw [heq]
      exact div_nonneg (by linarith) hD2.le
  · rcases hsign with hs | hs
    · rw [hs]
      have hle : (1 : ℝ) / ((convergentMatrix a 1 1 : ℝ) *
          ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ))) ≤ 1 := by
        rw [div_le_one hD2]
        exact hD2ge
      linarith
    · rw [hs]
      have hneg : (-1 : ℝ) / ((convergentMatrix a 1 1 : ℝ) *
          ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ))) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by norm_num) hD2.le
      linarith

/-- The Gauss–Kuzmin density. -/
private noncomputable def gkDensity (x : ℝ) : ℝ := 1 / (log 2 * (1 + x))

/-- A cubic bump supported in `Set.Icc u v`. -/
private noncomputable def bump (u v m x : ℝ) : ℝ :=
  if x ∈ Set.Icc u v then (x - u) * (x - v) * (x - m) else 0

/-- An antiderivative of the Gauss–Kuzmin density. -/
private noncomputable def gkAntideriv (x : ℝ) : ℝ := log (1 + x) / log 2

/-- The Gauss–Kuzmin density is continuous on `[0, 2]`. -/
private theorem gkDensity_continuousOn : ContinuousOn gkDensity (Set.Icc 0 2) := by
  have hlog : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hden : ∀ x ∈ Set.Icc (0 : ℝ) 2, log 2 * (1 + x) ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hx2⟩ := hx
    exact ne_of_gt (mul_pos hlog (by linarith))
  exact ContinuousOn.div continuousOn_const
    (continuousOn_const.mul (continuousOn_id.const_add 1)) hden

/-- The antiderivative has the Gauss–Kuzmin density as its derivative. -/
private theorem hasDerivAt_gkAntideriv (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt gkAntideriv (gkDensity x) x := by
  have h1x : (1 : ℝ) + x ≠ 0 := ne_of_gt (by linarith)
  have hlog2 : (log 2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hbase : HasDerivAt (fun x : ℝ => (1 : ℝ) + x) 1 x :=
    HasDerivAt.const_add 1 (hasDerivAt_id x)
  have hlog : HasDerivAt (fun x : ℝ => log (1 + x)) (1 / (1 + x)) x :=
    HasDerivAt.log hbase h1x
  have hdiv : HasDerivAt (fun x : ℝ => log (1 + x) / log 2) ((1 / (1 + x)) / log 2) x :=
    HasDerivAt.div_const hlog (log 2)
  have heq : (1 / (1 + x)) / log 2 = gkDensity x := by
    simp only [gkDensity, div_div]
    congr 1
    ring
  rw [heq] at hdiv
  exact hdiv

/-- The integral of the Gauss–Kuzmin density over an interval in `[0, 2]`. -/
private theorem integral_gkDensity_uIcc (a b : ℝ) (ha0 : 0 ≤ a) (hb2 : b ≤ 2)
    (hb0 : 0 ≤ b) (ha2 : a ≤ 2) :
    ∫ x in a..b, gkDensity x = gkAntideriv b - gkAntideriv a := by
  have hsub : Set.uIcc a b ⊆ Set.Icc 0 2 := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
  · intro x hx
    have hx0 : 0 ≤ x := (hsub hx).1
    exact hasDerivAt_gkAntideriv x hx0
  · exact ContinuousOn.intervalIntegrable (gkDensity_continuousOn.mono hsub)

/-- Antiderivative differences as log ratios. -/
private theorem gkAntideriv_sub (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    gkAntideriv β - gkAntideriv α = log ((1 + β) / (1 + α)) / log 2 := by
  have h1α : (1 : ℝ) + α ≠ 0 := ne_of_gt (by linarith)
  have h1β : (1 : ℝ) + β ≠ 0 := ne_of_gt (by linarith)
  simp only [gkAntideriv, Real.log_div h1β h1α, sub_div]

/-- Both interval sides have the same log ratio. -/
private theorem fundInterval_ratio_eq (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) (hne : a ≠ []) :
    (1 + ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
      ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
        (convergentMatrix a 1 1 : ℝ))))) /
      (1 + ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ))) =
    (1 + ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
      ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 1 0 : ℝ) +
        (convergentMatrix a 1 1 : ℝ))))) /
      (1 + ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ))) := by
  obtain ⟨h00, h0001, h01, h0111, h01ge, h10, h1011, h10ge, h11⟩ :=
    entries_of_pos_ne_nil a ha hne
  have hQ : (0 : ℝ) < (convergentMatrix a 1 1 : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one h11
  have hP : (0 : ℝ) ≤ (convergentMatrix a 0 1 : ℝ) := by exact_mod_cast h01
  have hR : (0 : ℝ) ≤ (convergentMatrix a 1 0 : ℝ) := by exact_mod_cast h10
  have hQ0 : (convergentMatrix a 1 1 : ℝ) ≠ 0 := ne_of_gt hQ
  have hPQ0 : (convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ) ≠ 0 :=
    ne_of_gt (by linarith)
  have hRQ0 : (convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ) ≠ 0 :=
    ne_of_gt (by linarith)
  have h1α1 : (1 : ℝ) + (convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) ≠ 0 :=
    ne_of_gt (by positivity)
  have h1α2 : (1 : ℝ) + (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) ≠ 0 :=
    ne_of_gt (by positivity)
  field_simp
  ring

/-- The Gauss–Kuzmin integral over an increasing endpoint interval. -/
private theorem integral_gkDensity_fundInterval_of_lt (α β : ℝ)
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) (hlt : α < β) :
    ∫ x in fundInterval α β, gkDensity x = gkAntideriv β - gkAntideriv α := by
  rw [fundInterval_of_lt hlt, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hlt.le]
  exact integral_gkDensity_uIcc α β hα0 hβ2 hβ0 hα2

/-- The Gauss–Kuzmin integral over a decreasing endpoint interval. -/
private theorem integral_gkDensity_fundInterval_of_gt (α β : ℝ)
    (hα0 : 0 ≤ α) (hα2 : α ≤ 2) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) (hgt : β < α) :
    ∫ x in fundInterval α β, gkDensity x = gkAntideriv α - gkAntideriv β := by
  have hIoc : fundInterval α β = Set.Ioc β α := by
    simp only [fundInterval]
    split_ifs with h
    · exact absurd h (not_lt.mpr hgt.le)
    · rfl
  rw [hIoc, ← intervalIntegral.integral_of_le hgt.le]
  exact integral_gkDensity_uIcc β α hβ0 hα2 hα0 hβ2

/-- The Gauss–Kuzmin density integrates symmetrically over reversed cylinders. -/
private theorem integral_gkDensity_reverse (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    ∫ x in cfCylinder a, gkDensity x = ∫ x in cfCylinder a.reverse, gkDensity x := by
  by_cases hne : a = []
  · subst hne
    simp
  · rw [setIntegral_congr_set (ae_eq_fundInterval_of_self a ha),
      setIntegral_congr_set (ae_eq_fundInterval_of_reverse a ha)]
    obtain ⟨bα10, bα11, bβ10, bβ12, bα20, bα21, bβ20, bβ22⟩ :=
      fundInterval_endpoints_mem a ha hne
    obtain ⟨-, -, h01, -, -, h10, -, -, h11⟩ := entries_of_pos_ne_nil a ha hne
    have hQ : (0 : ℝ) < (convergentMatrix a 1 1 : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one h11
    have hP : (0 : ℝ) ≤ (convergentMatrix a 0 1 : ℝ) := by exact_mod_cast h01
    have hR : (0 : ℝ) ≤ (convergentMatrix a 1 0 : ℝ) := by exact_mod_cast h10
    have hD1 : (0 : ℝ) < (convergentMatrix a 1 1 : ℝ) *
        ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ)) :=
      mul_pos hQ (by linarith)
    have hD2 : (0 : ℝ) < (convergentMatrix a 1 1 : ℝ) *
        ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ)) :=
      mul_pos hQ (by linarith)
    have hFsgn : gkAntideriv ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) +
          (-1) ^ a.length / ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ)))) -
        gkAntideriv ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ)) =
        gkAntideriv ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) +
          (-1) ^ a.length / ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ)))) -
        gkAntideriv ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)) := by
      rw [gkAntideriv_sub _ _ bα10 bβ10, gkAntideriv_sub _ _ bα20 bβ20,
        fundInterval_ratio_eq a ha hne]
    have hsign : (-1 : ℝ) ^ a.length = 1 ∨ (-1 : ℝ) ^ a.length = -1 := by
      rcases Nat.even_or_odd a.length with he | ho
      · exact Or.inl (Even.neg_one_pow he)
      · exact Or.inr (Odd.neg_one_pow ho)
    rcases hsign with hs | hs
    · have hlt1 : (convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) <
          (convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
          ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
            (convergentMatrix a 1 1 : ℝ))) := by
        rw [hs]
        have hpos : (0 : ℝ) < 1 / ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ))) :=
          one_div_pos.mpr hD1
        linarith
      have hlt2 : (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) <
          (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
          ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 1 0 : ℝ) +
            (convergentMatrix a 1 1 : ℝ))) := by
        rw [hs]
        have hpos : (0 : ℝ) < 1 / ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ))) :=
          one_div_pos.mpr hD2
        linarith
      have e1 := integral_gkDensity_fundInterval_of_lt _ _ bα10 (by linarith) bβ10 bβ12 hlt1
      have e2 := integral_gkDensity_fundInterval_of_lt _ _ bα20 (by linarith) bβ20 bβ22 hlt2
      rw [e1, e2]
      exact hFsgn.symm
    · have hgt1 : (convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) +
          (-1) ^ a.length / ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ))) <
          (convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) := by
        rw [hs]
        have hneg : (-1 : ℝ) / ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ))) < 0 :=
          div_neg_of_neg_of_pos (by norm_num) hD1
        linarith
      have hgt2 : (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) +
          (-1) ^ a.length / ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ))) <
          (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) := by
        rw [hs]
        have hneg : (-1 : ℝ) / ((convergentMatrix a 1 1 : ℝ) *
            ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ))) < 0 :=
          div_neg_of_neg_of_pos (by norm_num) hD2
        linarith
      have e1 := integral_gkDensity_fundInterval_of_gt _ _ bα10 (by linarith) bβ10 bβ12 hgt1
      have e2 := integral_gkDensity_fundInterval_of_gt _ _ bα20 (by linarith) bβ20 bβ22 hgt2
      rw [e1, e2]
      linarith [hFsgn]

/-- The bump is continuous. -/
private theorem bump_continuous (u v m : ℝ) (huv : u < v) :
    Continuous (bump u v m) := by
  have hfront : ∀ a ∈ frontier {x | x ∈ Set.Icc u v},
      (a - u) * (a - v) * (a - m) = 0 := by
    intro a ha
    rw [Set.ofPred_mem_eq, frontier_Icc huv.le] at ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> ring
  have hpoly : Continuous (fun x : ℝ => (x - u) * (x - v) * (x - m)) :=
    ((continuous_id.sub continuous_const).mul
      (continuous_id.sub continuous_const)).mul
      (continuous_id.sub continuous_const)
  exact Continuous.if hfront hpoly continuous_const

/-- The bump vanishes outside its interval. -/
private theorem bump_eq_zero_outside (u v m x : ℝ) (hx : x ∉ Set.Icc u v) :
    bump u v m x = 0 := by
  simp [bump, hx]

/-- The support of a scaled bump lies in its interval. -/
private theorem bump_support_subset (u v m ε : ℝ) :
    Function.support (fun x => ε * bump u v m x) ⊆ Set.Icc u v := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxI
  exact hx (by simp [bump_eq_zero_outside u v m x hxI])

/-- A scaled bump is integrable. -/
private theorem bump_integrable (u v m ε : ℝ) (huv : u < v) :
    Integrable (fun x => ε * bump u v m x) volume := by
  have hcs : HasCompactSupport (fun x => ε * bump u v m x) := by
    change IsCompact (tsupport _)
    exact IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
      (closure_minimal (bump_support_subset u v m ε) isClosed_Icc)
  exact (bump_continuous u v m huv).const_mul ε |>.integrable_of_hasCompactSupport hcs

/-- An antiderivative of the bump polynomial. -/
private noncomputable def bumpAntideriv (m r x : ℝ) : ℝ :=
  (x - m) ^ 4 / 4 - r ^ 2 * (x - m) ^ 2 / 2

/-- The bump polynomial is the derivative of its antiderivative. -/
private theorem hasDerivAt_bumpAntideriv (u v m r x : ℝ) (hum : u = m - r)
    (hvm : v = m + r) :
    HasDerivAt (bumpAntideriv m r) ((x - u) * (x - v) * (x - m)) x := by
  have hsub : HasDerivAt (fun x : ℝ => x - m) 1 x :=
    HasDerivAt.sub_const _ (hasDerivAt_id x)
  have h4 : HasDerivAt (fun x : ℝ => (x - m) ^ 4 / 4) ((x - m) ^ 3) x := by
    have h := (hsub.pow 4).div_const (4 : ℝ)
    have e1 : (4 : ℕ) - 1 = 3 := by norm_num
    rw [e1] at h
    norm_num at h
    exact h
  have h2 : HasDerivAt (fun x : ℝ => r ^ 2 * (x - m) ^ 2 / 2) (r ^ 2 * (x - m)) x := by
    have h := ((hsub.pow 2).const_mul (r ^ 2)).div_const (2 : ℝ)
    have e1 : (2 : ℕ) - 1 = 1 := by norm_num
    rw [e1] at h
    norm_num at h
    rw [show r ^ 2 * (2 * (x - m)) / 2 = r ^ 2 * (x - m) from by ring] at h
    exact h
  have hF := h4.sub h2
  have heq : (x - u) * (x - v) * (x - m) = (x - m) ^ 3 - r ^ 2 * (x - m) := by
    rw [hum, hvm]
    ring
  rw [heq]
  exact hF

/-- The bump integrates to zero over its interval. -/
private theorem integral_bump_Icc (u v m r : ℝ) (huv : u < v) (hum : u = m - r)
    (hvm : v = m + r) : ∫ x in Set.Icc u v, bump u v m x = 0 := by
  rw [integral_Icc_eq_integral_Ioc]
  have hcongr : ∀ x ∈ Set.Ioc u v, bump u v m x = (x - u) * (x - v) * (x - m) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc u v := ⟨hx.1.le, hx.2⟩
    simp [bump, hxIcc]
  rw [setIntegral_congr_ae measurableSet_Ioc (Filter.Eventually.of_forall hcongr),
    ← intervalIntegral.integral_of_le huv.le]
  have hpoly : ContinuousOn (fun x : ℝ => (x - u) * (x - v) * (x - m)) (Set.uIcc u v) :=
    (((continuousOn_id.sub continuousOn_const).mul
      (continuousOn_id.sub continuousOn_const)).mul
      (continuousOn_id.sub continuousOn_const))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := bumpAntideriv m r) (f' := fun x => (x - u) * (x - v) * (x - m))
    (fun x _ => hasDerivAt_bumpAntideriv u v m r x hum hvm)
    (ContinuousOn.intervalIntegrable hpoly)
  rw [hFTC]
  simp only [bumpAntideriv]
  rw [show v - m = r from by linarith, show u - m = -r from by linarith]
  ring

/-- A short string either prefixes the bump cylinder or is disjoint from it. -/
private theorem subset_or_disjoint_of_length_le (c : List ℕ) (N : ℕ)
    (hc : c.length = N + 1) (a : List ℕ) (hlen : a.length ≤ N) :
    cfCylinder c ⊆ cfCylinder a ∨ Disjoint (cfCylinder a) (cfCylinder c) := by
  by_cases htake : c.take a.length = a
  · left
    intro x hxc
    obtain ⟨hx01, hxdig⟩ := hxc
    refine ⟨hx01, fun j hj => ?_⟩
    have hjc : j < c.length := by omega
    have h1 := hxdig j hjc
    have htake_len : (c.take a.length).length = a.length := by
      rw [List.length_take, hc]
      omega
    have hj' : j < (c.take a.length).length := by omega
    have h3 : (c.take a.length)[j]'hj' = c[j]'hjc := List.getElem_take
    simp only [htake] at h3
    rw [h1]
    congr 1
    exact_mod_cast h3.symm
  · right
    rw [Set.disjoint_left]
    intro x hxa hxc
    have htake_len : (c.take a.length).length = a.length := by
      rw [List.length_take, hc]
      omega
    have hex : ∃ (j : ℕ) (hj1 : j < (c.take a.length).length) (hj2 : j < a.length),
        (c.take a.length)[j]'hj1 ≠ a[j]'hj2 := by
      by_contra hall
      push Not at hall
      exact htake (List.ext_getElem htake_len hall)
    obtain ⟨j, hj1, hj2, hne⟩ := hex
    have hjc : j < c.length := by omega
    have ha_digit := hxa.2 j hj2
    have hc_digit := hxc.2 j hjc
    rw [ha_digit] at hc_digit
    have hcast : a[j]'hj2 = c[j]'hjc := Nat.cast_inj.mp (Option.some.inj hc_digit)
    have h3 : (c.take a.length)[j]'hj1 = c[j]'hjc := List.getElem_take
    exact hne (h3.trans hcast.symm)

/-- The bump integrates to zero over every short cylinder. -/
private theorem integral_bump_cylinder (c : List ℕ) (N : ℕ) (hc : c.length = N + 1)
    (u v m r : ℝ) (hsub : Set.Icc u v ⊆ cfCylinder c) (a : List ℕ) (hlen : a.length ≤ N)
    (huv : u < v) (hum : u = m - r) (hvm : v = m + r) :
    ∫ x in cfCylinder a, bump u v m x = 0 := by
  rcases subset_or_disjoint_of_length_le c N hc a hlen with hsub' | hdisj
  · have h1 : ∫ x in cfCylinder a, bump u v m x = ∫ x, bump u v m x := by
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      exact Filter.Eventually.of_forall (fun x hx =>
        bump_eq_zero_outside u v m x (fun hIcc => hx (hsub' (hsub hIcc))))
    have h2 : (∫ x, bump u v m x) = ∫ x in Set.Icc u v, bump u v m x := by
      symm
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      exact Filter.Eventually.of_forall (fun x hx => bump_eq_zero_outside u v m x hx)
    rw [h1, h2]
    exact integral_bump_Icc u v m r huv hum hvm
  · have hvanish : ∀ x ∈ cfCylinder a, bump u v m x = 0 := by
      intro x hxa
      have hxc : x ∉ cfCylinder c := Set.disjoint_left.mp hdisj hxa
      exact bump_eq_zero_outside u v m x (fun hIcc => hxc (hsub hIcc))
    have hmeas : MeasurableSet {x | bump u v m x = 0} :=
      (bump_continuous u v m huv).measurable (measurableSet_singleton 0)
    have hae : (fun x => bump u v m x) =ᵐ[volume.restrict (cfCylinder a)] 0 :=
      (ae_restrict_iff hmeas).2 (Filter.Eventually.of_forall hvanish)
    exact integral_eq_zero_of_ae hae

set_option linter.unusedVariables false in
/-- **Symmetry up to a fixed length does not force the Gauss–Kuzmin density.** Write $I(a)$ for
the fundamental interval of a string $a$ and $\overleftarrow{a}$ for the reverse of $a$. For every
integer $N \ge 1$ there is a real function $f$, continuous and nonnegative on $[0, 1]$ with
$\int_0^1 f(x)\,dx = 1$, such that $\int_{I(a)} f(x)\,dx = \int_{I(\overleftarrow{a})} f(x)\,dx$
for every string $a$ of positive integers of length at most $N$, but
$f(x) \ne \frac{1}{\log 2 \cdot (1 + x)}$ for some $x \in [0, 1]$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Theorem 2 (`integers-2025-A89-thm-2`). -/
public theorem exists_reverse_symmetric_density_ne_gaussKuzmin (N : ℕ) (hN : 1 ≤ N) :
    ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc 0 1) ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) ∧
      ∫ x in (0 : ℝ)..1, f x = 1 ∧
      (∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length ≤ N →
        ∫ x in cfCylinder a, f x = ∫ x in cfCylinder a.reverse, f x) ∧
      ∃ x ∈ Set.Icc (0 : ℝ) 1, f x ≠ 1 / (log 2 * (1 + x)) := by
  obtain ⟨α, β, hα0, hαβ, hβ1, hsubJ⟩ := exists_Ioo_subset_cfCylinder_replicate (N + 1)
  have hc_len : (List.replicate (N + 1) 1).length = N + 1 := by simp
  set m₀ : ℝ := (α + β) / 2 with hm₀
  set r₀ : ℝ := (β - α) / 4 with hr₀
  have hr0 : 0 < r₀ := by simp [hr₀]; linarith
  set u : ℝ := m₀ - r₀ with hu
  set v : ℝ := m₀ + r₀ with hv
  have huv : u < v := by simp [hu, hv]; linarith
  have huIoo : u ∈ Set.Ioo α β := by
    constructor <;> simp [hu, hm₀, hr₀] <;> linarith
  have hvIoo : v ∈ Set.Ioo α β := by
    constructor <;> simp [hv, hm₀, hr₀] <;> linarith
  have hIcc_sub : Set.Icc u v ⊆ Set.Ioo α β := by
    intro x hx
    obtain ⟨hxu, hxv⟩ := hx
    exact ⟨lt_of_lt_of_le huIoo.1 hxu, lt_of_le_of_lt hxv hvIoo.2⟩
  have hIcc_cyl : Set.Icc u v ⊆ cfCylinder (List.replicate (N + 1) 1) :=
    hIcc_sub.trans hsubJ
  have hu0 : 0 ≤ u := le_trans hα0.le huIoo.1.le
  have hv1 : v ≤ 1 := le_trans hvIoo.2.le hβ1.le
  have hu0' : 0 < u := lt_of_lt_of_le hα0 huIoo.1.le
  have hv1' : v < 1 := lt_of_le_of_lt hvIoo.2.le hβ1
  have hIoc : Set.Icc u v ⊆ Set.Ioc 0 1 := by
    intro x hx
    obtain ⟨hxu, hxv⟩ := hx
    exact ⟨lt_of_lt_of_le hu0' hxu, (lt_of_le_of_lt hxv hv1').le⟩
  set M : ℝ := (v - u) ^ 3 with hM
  have hM0 : 0 < M := by rw [hM]; exact pow_pos (sub_pos.mpr huv) 3
  have hlog : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlog0 : (log 2 : ℝ) ≠ 0 := ne_of_gt hlog
  set ε : ℝ := 1 / (4 * log 2 * M) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hMε : ε * M = 1 / (4 * log 2) := by
    have ne1 : (4 : ℝ) * log 2 * M ≠ 0 := ne_of_gt (by positivity)
    have ne2 : (4 : ℝ) * log 2 ≠ 0 := ne_of_gt (by positivity)
    simp [hε]
    field_simp
  refine ⟨fun x => gkDensity x + ε * bump u v m₀ x, ?_, ?_, ?_, ?_, ?_⟩
  · have hg : ContinuousOn gkDensity (Set.Icc 0 1) :=
      gkDensity_continuousOn.mono (Set.Icc_subset_Icc le_rfl one_le_two)
    have hb : ContinuousOn (fun x => ε * bump u v m₀ x) (Set.Icc 0 1) :=
      (bump_continuous u v m₀ huv).continuousOn.const_mul ε
    exact hg.add hb
  · intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have h1x : (1 : ℝ) + x ≤ 2 := by linarith
    have h1x0 : (0 : ℝ) < 1 + x := by linarith
    have hlog1x : log 2 * (1 + x) ≤ 2 * log 2 := by nlinarith [hlog, h1x]
    have hgk : 1 / (2 * log 2) ≤ gkDensity x := by
      simp only [gkDensity]
      apply one_div_le_one_div_of_le
      · positivity
      · linarith [hlog1x]
    have hbM : |bump u v m₀ x| ≤ M := by
      by_cases hxI : x ∈ Set.Icc u v
      · obtain ⟨hxu, hxv⟩ := Set.mem_Icc.mp hxI
        have hm0lo : u ≤ m₀ := by simp [hu]; linarith
        have hm0hi : m₀ ≤ v := by simp [hv]; linarith
        have e1 : |x - u| ≤ v - u := abs_le.mpr ⟨by linarith, by linarith⟩
        have e2 : |x - v| ≤ v - u := abs_le.mpr ⟨by linarith, by linarith⟩
        have e3 : |x - m₀| ≤ v - u := abs_le.mpr ⟨by linarith, by linarith⟩
        have hbv : bump u v m₀ x = (x - u) * (x - v) * (x - m₀) := by simp [bump, hxI]
        rw [hbv, hM, abs_mul, abs_mul]
        have hvu0 : (0 : ℝ) ≤ v - u := (sub_pos.mpr huv).le
        calc |x - u| * |x - v| * |x - m₀|
            ≤ (v - u) * (v - u) * (v - u) := by
              apply mul_le_mul _ e3 (abs_nonneg _) (mul_nonneg hvu0 hvu0)
              exact mul_le_mul e1 e2 (abs_nonneg _) hvu0
          _ = (v - u) ^ 3 := by ring
      · rw [bump_eq_zero_outside u v m₀ x hxI]
        simpa using hM0.le
    have hbump : |ε * bump u v m₀ x| ≤ 1 / (4 * log 2) := by
      rw [abs_mul, abs_of_pos hε0]
      calc ε * |bump u v m₀ x| ≤ ε * M := mul_le_mul_of_nonneg_left hbM hε0.le
        _ = 1 / (4 * log 2) := hMε
    have hεb : -(1 / (4 * log 2)) ≤ ε * bump u v m₀ x := by
      have h := neg_le_of_abs_le hbump
      linarith [h]
    have hpos : (0 : ℝ) < 1 / (4 * log 2) := by positivity
    have heq : (1 : ℝ) / (2 * log 2) - 1 / (4 * log 2) = 1 / (4 * log 2) := by
      field_simp
      ring
    change (0 : ℝ) ≤ gkDensity x + ε * bump u v m₀ x
    linarith [hgk, hεb, heq, hpos]
  · have hsub01 : Set.uIcc (0 : ℝ) 1 ⊆ Set.Icc 0 2 := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
    have hgInt : IntervalIntegrable gkDensity volume 0 1 :=
      ContinuousOn.intervalIntegrable (gkDensity_continuousOn.mono hsub01)
    have hbInt : IntervalIntegrable (fun x => ε * bump u v m₀ x) volume 0 1 :=
      (bump_integrable u v m₀ ε huv).intervalIntegrable
    have hsplit : ∫ x in (0 : ℝ)..1, (gkDensity x + ε * bump u v m₀ x) =
        (∫ x in (0 : ℝ)..1, gkDensity x) + ∫ x in (0 : ℝ)..1, ε * bump u v m₀ x :=
      intervalIntegral.integral_add hgInt hbInt
    have hgk1 : ∫ x in (0 : ℝ)..1, gkDensity x = 1 := by
      have h := integral_gkDensity_uIcc (0 : ℝ) 1 le_rfl (by norm_num) zero_le_one
        (by norm_num)
      rw [h]
      simp only [gkAntideriv]
      rw [show (1 : ℝ) + 1 = 2 from by norm_num, show (1 : ℝ) + 0 = 1 from by norm_num,
        Real.log_one]
      simp [div_self hlog0]
    have hbump0 : ∫ x in (0 : ℝ)..1, ε * bump u v m₀ x = 0 := by
      rw [intervalIntegral.integral_const_mul]
      have hb0 : ∫ x in (0 : ℝ)..1, bump u v m₀ x = 0 := by
        rw [intervalIntegral.integral_of_le zero_le_one]
        have h1 : ∫ x in Set.Ioc (0 : ℝ) 1, bump u v m₀ x = ∫ x, bump u v m₀ x := by
          apply setIntegral_eq_integral_of_ae_compl_eq_zero
          apply Filter.Eventually.of_forall
          intro x hx
          apply bump_eq_zero_outside
          intro hIcc
          exact hx (hIoc hIcc)
        have h2 : (∫ x, bump u v m₀ x) = ∫ x in Set.Icc u v, bump u v m₀ x := by
          symm
          apply setIntegral_eq_integral_of_ae_compl_eq_zero
          exact Filter.Eventually.of_forall (fun x hx => bump_eq_zero_outside u v m₀ x hx)
        rw [h1, h2]
        exact integral_bump_Icc u v m₀ r₀ huv hu hv
      rw [hb0, mul_zero]
    change ∫ x in (0 : ℝ)..1, (gkDensity x + ε * bump u v m₀ x) = 1
    rw [hsplit, hgk1, hbump0, add_zero]
  · intro a ha hlen
    have ha_rev : ∀ x ∈ a.reverse, 0 < x := fun x hx => ha x (List.mem_reverse.mp hx)
    have hlen_rev : a.reverse.length ≤ N := by rw [List.length_reverse]; exact hlen
    by_cases hne : a = []
    · subst hne
      simp only [List.reverse_nil]
    · obtain ⟨bα10, bα11, bβ10, bβ12, bα20, bα21, bβ20, bβ22⟩ :=
        fundInterval_endpoints_mem a ha hne
      have hJ2 : fundInterval ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ))
          ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
            ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 1 0 : ℝ) +
              (convergentMatrix a 1 1 : ℝ)))) ⊆ Set.Icc 0 2 := by
        by_cases hlt : (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) <
            (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
            ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 1 0 : ℝ) +
              (convergentMatrix a 1 1 : ℝ)))
        · rw [fundInterval_of_lt hlt]
          intro x hx
          obtain ⟨hx1, hx2⟩ := hx
          constructor <;> linarith
        · have hIoc : fundInterval ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ))
              ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
              ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 1 0 : ℝ) +
                (convergentMatrix a 1 1 : ℝ)))) =
              Set.Ioc ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ) +
                (-1) ^ a.length / ((convergentMatrix a 1 1 : ℝ) *
                  ((convergentMatrix a 1 0 : ℝ) + (convergentMatrix a 1 1 : ℝ))))
                ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)) := by
            simp [fundInterval, hlt]
          rw [hIoc]
          intro x hx
          obtain ⟨hx1, hx2⟩ := hx
          constructor <;> linarith
      have hJ1 : fundInterval ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ))
          ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
            ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
              (convergentMatrix a 1 1 : ℝ)))) ⊆ Set.Icc 0 2 := by
        by_cases hlt : (convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) <
            (convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
            ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
              (convergentMatrix a 1 1 : ℝ)))
        · rw [fundInterval_of_lt hlt]
          intro x hx
          obtain ⟨hx1, hx2⟩ := hx
          constructor <;> linarith
        · have hIoc : fundInterval ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ))
              ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
              ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
                (convergentMatrix a 1 1 : ℝ)))) =
              Set.Ioc ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) +
                (-1) ^ a.length / ((convergentMatrix a 1 1 : ℝ) *
                  ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ))))
                ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ)) := by
            simp [fundInterval, hlt]
          rw [hIoc]
          intro x hx
          obtain ⟨hx1, hx2⟩ := hx
          constructor <;> linarith
      have hgIcc : IntegrableOn gkDensity (Set.Icc 0 2) volume :=
        gkDensity_continuousOn.integrableOn_Icc
      have hgA : IntegrableOn gkDensity (cfCylinder a) volume :=
        (hgIcc.mono_set hJ2).congr_set_ae (ae_eq_fundInterval_of_self a ha)
      have hgR : IntegrableOn gkDensity (cfCylinder a.reverse) volume :=
        (hgIcc.mono_set hJ1).congr_set_ae (ae_eq_fundInterval_of_reverse a ha)
      have hbA : IntegrableOn (fun x => ε * bump u v m₀ x) (cfCylinder a) volume :=
        (bump_integrable u v m₀ ε huv).integrableOn
      have hbR : IntegrableOn (fun x => ε * bump u v m₀ x)
          (cfCylinder a.reverse) volume :=
        (bump_integrable u v m₀ ε huv).integrableOn
      have splitA : ∫ x in cfCylinder a, (gkDensity x + ε * bump u v m₀ x) =
          (∫ x in cfCylinder a, gkDensity x) + ∫ x in cfCylinder a, ε * bump u v m₀ x :=
        integral_add hgA hbA
      have splitR : ∫ x in cfCylinder a.reverse, (gkDensity x + ε * bump u v m₀ x) =
          (∫ x in cfCylinder a.reverse, gkDensity x) +
          ∫ x in cfCylinder a.reverse, ε * bump u v m₀ x :=
        integral_add hgR hbR
      have bumpA : ∫ x in cfCylinder a, ε * bump u v m₀ x = 0 := by
        rw [integral_const_mul]
        rw [integral_bump_cylinder (List.replicate (N + 1) 1) N hc_len u v m₀ r₀ hIcc_cyl a
          hlen huv hu hv]
        exact mul_zero ε
      have bumpR : ∫ x in cfCylinder a.reverse, ε * bump u v m₀ x = 0 := by
        rw [integral_const_mul]
        rw [integral_bump_cylinder (List.replicate (N + 1) 1) N hc_len u v m₀ r₀ hIcc_cyl
          a.reverse hlen_rev huv hu hv]
        exact mul_zero ε
      change ∫ x in cfCylinder a, (gkDensity x + ε * bump u v m₀ x) =
        ∫ x in cfCylinder a.reverse, (gkDensity x + ε * bump u v m₀ x)
      rw [splitA, splitR, bumpA, bumpR, add_zero, add_zero]
      exact integral_gkDensity_reverse a ha
  · have hm0v : m₀ ≤ v := by simp [hv]; linarith
    have hm0u : u ≤ m₀ := by simp [hu]; linarith
    have hu1 : u ≤ 1 := le_trans huv.le hv1
    have hm01 : m₀ ≤ 1 := le_trans hm0v hv1
    have hm00 : 0 ≤ m₀ := le_trans hu0 hm0u
    have hx0mem : (u + m₀) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith
    refine ⟨(u + m₀) / 2, hx0mem, ?_⟩
    have hxI : (u + m₀) / 2 ∈ Set.Icc u v := by
      constructor <;> linarith
    have h1 : (u + m₀) / 2 - u ≠ 0 := by
      have heq : (u + m₀) / 2 - u = r₀ / 2 := by simp [hu]; ring
      rw [heq]
      exact ne_of_gt (by linarith)
    have h2 : (u + m₀) / 2 - v ≠ 0 := by
      have hlt : (u + m₀) / 2 < v := by linarith
      exact ne_of_lt (by linarith)
    have h3 : (u + m₀) / 2 - m₀ ≠ 0 := by
      have heq : (u + m₀) / 2 - m₀ = -(r₀ / 2) := by simp [hu]; ring
      rw [heq]
      exact ne_of_lt (by linarith)
    have hbump0 : bump u v m₀ ((u + m₀) / 2) ≠ 0 := by
      have hbv : bump u v m₀ ((u + m₀) / 2) =
          ((u + m₀) / 2 - u) * ((u + m₀) / 2 - v) * ((u + m₀) / 2 - m₀) := by
        simp [bump, hxI]
      rw [hbv]
      exact mul_ne_zero (mul_ne_zero h1 h2) h3
    change gkDensity ((u + m₀) / 2) + ε * bump u v m₀ ((u + m₀) / 2) ≠
      1 / (log 2 * (1 + (u + m₀) / 2))
    have hgkeq : gkDensity ((u + m₀) / 2) = 1 / (log 2 * (1 + (u + m₀) / 2)) := rfl
    rw [hgkeq]
    have hne : ε * bump u v m₀ ((u + m₀) / 2) ≠ 0 :=
      mul_ne_zero (ne_of_gt hε0) hbump0
    intro hcon
    have h0 : ε * bump u v m₀ ((u + m₀) / 2) = 0 := by linarith [hcon]
    exact hne h0

end

end MetaMathlibExt
