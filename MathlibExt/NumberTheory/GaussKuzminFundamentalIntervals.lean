/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Computation.Translations
public import Mathlib.Data.Seq.Basic
public import MathlibExt.NumberTheory.GaussKuzminSymmetry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Fundamental intervals of reversed and extended strings

This module proves that the fundamental interval of a string of positive
integers, and of its reversals and one-digit extensions, is almost everywhere
equal to the half-open interval between its convergent endpoints.
-/

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory Filter Topology Real

namespace cfCylinder_reverse_append_cons_ae_eq

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

/-- The left endpoint associated with a string. -/
private noncomputable def endA (a : List ℕ) : ℝ :=
  (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)

/-- The right endpoint associated with a string. -/
private noncomputable def endB (a : List ℕ) : ℝ :=
  ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 0 0 : ℝ)) /
    ((convergentMatrix a 1 1 : ℝ) + (convergentMatrix a 1 0 : ℝ))

private theorem entries_pos' (a : List ℕ) (ha : ∀ x ∈ a, 1 ≤ x) :
    0 ≤ convergentMatrix a 0 0 ∧ 0 ≤ convergentMatrix a 0 1 ∧
    0 ≤ convergentMatrix a 1 0 ∧ 1 ≤ convergentMatrix a 1 1 ∧
    convergentMatrix a 0 1 ≤ convergentMatrix a 1 1 ∧
    convergentMatrix a 0 1 + convergentMatrix a 0 0 ≤
      convergentMatrix a 1 1 + convergentMatrix a 1 0 ∧
    1 ≤ convergentMatrix a 0 1 + convergentMatrix a 0 0 := by
  induction a with
  | nil => simp [convergentMatrix_nil]
  | cons t a ih =>
    have ht : 1 ≤ t := ha t (by simp)
    have ha' : ∀ x ∈ a, 1 ≤ x := fun x hx => ha x (by simp [hx])
    obtain ⟨h00, h01, h10, h11, hle1, hsum, hsum1⟩ := ih ha'
    have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast ht
    have hpos10 : (0 : ℤ) ≤ t * convergentMatrix a 1 0 := by positivity
    have hpos11 : (0 : ℤ) ≤ t * convergentMatrix a 1 1 := by positivity
    have hge11 : convergentMatrix a 1 1 ≤ (t : ℤ) * convergentMatrix a 1 1 :=
      le_mul_of_one_le_left (by omega) ht1
    rw [cm_cons_00, cm_cons_01, cm_cons_10, cm_cons_11]
    refine ⟨h10, le_of_lt (lt_of_lt_of_le zero_lt_one h11), ?_, ?_, ?_, ?_, ?_⟩
    · positivity
    · linarith [hge11, h11]
    · linarith [hge11, h01]
    · nlinarith [hsum, ht1, h11, h10, hpos10, hpos11]
    · linarith [h11, h10]

private theorem endpoint_bounds (a : List ℕ) (ha : ∀ x ∈ a, 1 ≤ x) :
    0 ≤ endA a ∧ endA a ≤ 1 ∧ 0 < endB a ∧ endB a ≤ 1 ∧
    (0:ℝ) < (convergentMatrix a 1 1 : ℝ) ∧
    (0:ℝ) < (convergentMatrix a 1 1 : ℝ) + (convergentMatrix a 1 0 : ℝ) := by
  obtain ⟨h00, h01, h10, h11, hle1, hsum, hsum1⟩ := entries_pos' a ha
  have hq : (0:ℝ) < (convergentMatrix a 1 1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one h11)
  have hq' : (0:ℝ) < (convergentMatrix a 1 1 : ℝ) + (convergentMatrix a 1 0 : ℝ) := by
    have : (0:ℝ) ≤ (convergentMatrix a 1 0 : ℝ) := by exact_mod_cast h10
    linarith
  refine ⟨?_, ?_, ?_, ?_, hq, hq'⟩
  · unfold endA; positivity
  · unfold endA; rw [div_le_one hq]; exact_mod_cast hle1
  · unfold endB; apply div_pos
    · have h1 : (0:ℝ) ≤ (convergentMatrix a 0 1 : ℝ) := by exact_mod_cast h01
      have h2 : (0:ℝ) ≤ (convergentMatrix a 0 0 : ℝ) := by exact_mod_cast h00
      have hsum' : (1:ℝ) ≤ (convergentMatrix a 0 1 : ℝ) +
          (convergentMatrix a 0 0 : ℝ) := by exact_mod_cast hsum1
      linarith
    · exact hq'
  · unfold endB; rw [div_le_one hq']
    have hsum' : (convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 0 0 : ℝ) ≤
        (convergentMatrix a 1 1 : ℝ) + (convergentMatrix a 1 0 : ℝ) := by exact_mod_cast hsum
    exact hsum'

private theorem endA_cons (t : ℕ) (a : List ℕ) (ha : ∀ x ∈ a, 1 ≤ x) :
    endA (t :: a) = 1 / ((t : ℝ) + endA a) := by
  obtain ⟨-, -, -, -, hqpos, -⟩ := endpoint_bounds a ha
  have hq : (convergentMatrix a 1 1 : ℝ) ≠ 0 := ne_of_gt hqpos
  rw [endA, cm_cons_01, cm_cons_11, endA]
  field_simp
  congr 1
  push_cast
  ring

private theorem endB_cons (t : ℕ) (a : List ℕ) (ha : ∀ x ∈ a, 1 ≤ x) :
    endB (t :: a) = 1 / ((t : ℝ) + endB a) := by
  obtain ⟨-, -, -, -, -, hqpos⟩ := endpoint_bounds a ha
  have hq : ((convergentMatrix a 1 1 : ℝ) + (convergentMatrix a 1 0 : ℝ)) ≠ 0 := ne_of_gt hqpos
  rw [endB, cm_cons_01, cm_cons_00, cm_cons_11, cm_cons_10, endB]
  field_simp
  congr 1
  push_cast
  ring

private theorem cyl_mem_cons {t : ℕ} {a : List ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hfloor : ⌊x⁻¹⌋ = (t : ℤ)) (hy : Int.fract x⁻¹ ∈ cfCylinder a) :
    x ∈ cfCylinder (t :: a) := by
  obtain ⟨-, hydig⟩ := hy
  refine ⟨⟨hx0.le, hx1⟩, fun i hi => ?_⟩
  cases i with
  | zero =>
    have h0 := partDens_zero x hx0 hx1
    rw [hfloor] at h0
    simpa using h0
  | succ i =>
    have hi' : i < a.length := by
      have := hi
      simp only [List.length_cons] at this
      omega
    have h1 := partDens_succ x hx0 hx1 i
    have h2 := partDens_eq_of_fract x⁻¹ i
    rw [h1, h2]
    have h3 := hydig i hi'
    simpa [List.getElem_cons_succ] using h3

private theorem cyl_of_mem_cons {t : ℕ} {a : List ℕ} {x : ℝ} (hx : x ∈ cfCylinder (t :: a)) :
    0 < x ∧ x < 1 ∧ ⌊x⁻¹⌋ = (t : ℤ) ∧ Int.fract x⁻¹ ∈ cfCylinder a := by
  obtain ⟨⟨hx0, hx1⟩, hdig⟩ := hx
  have hxpos : 0 < x := by
    by_contra h
    have hle : x ≤ 0 := not_lt.mp h
    have hxeq : x = 0 := le_antisymm hle hx0
    subst hxeq
    have h0 := hdig 0 (by simp)
    have hnil : (GenContFract.of (0 : ℝ)).partDens.get? 0 = none := by
      have hs : (GenContFract.of (0 : ℝ)).s = Stream'.Seq.nil := by
        simpa using GenContFract.of_s_of_int (K := ℝ) (0 : ℤ)
      change (Stream'.Seq.map GenContFract.Pair.b (GenContFract.of (0 : ℝ)).s).get? 0 = none
      rw [Stream'.Seq.map_get?, hs]
      rfl
    rw [hnil] at h0
    simp at h0
  have hfloor : ⌊x⁻¹⌋ = (t : ℤ) := by
    have h0 := hdig 0 (by simp)
    rw [partDens_zero x hxpos hx1] at h0
    have hcast : ((⌊x⁻¹⌋ : ℤ) : ℝ) = (t : ℝ) := Option.some.inj h0
    exact_mod_cast hcast
  refine ⟨hxpos, hx1, hfloor, ?_⟩
  refine ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, fun i hi => ?_⟩
  have h1 := partDens_succ x hxpos hx1 i
  have h2 := partDens_eq_of_fract x⁻¹ i
  rw [← h2, ← h1]
  have h3 := hdig (i + 1) (by simp [hi])
  simpa [List.getElem_cons_succ] using h3

private theorem cylinder_between (a : List ℕ) (ha : ∀ x ∈ a, 1 ≤ x) :
    (∀ x : ℝ, (endA a < x ∧ x < endB a) ∨ (endB a < x ∧ x < endA a) →
      x ∈ cfCylinder a) ∧
    (∀ x : ℝ, x ∈ cfCylinder a →
      (endA a ≤ x ∧ x ≤ endB a) ∨ (endB a ≤ x ∧ x ≤ endA a)) := by
  induction a with
  | nil =>
    have hA : endA [] = 0 := by simp [endA, convergentMatrix_nil]
    have hB : endB [] = 1 := by simp [endB, convergentMatrix_nil]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hA] at h1; rw [hB] at h2
        simp only [cfCylinder_nil, Set.mem_Ico]
        exact ⟨h1.le, h2⟩
      · rw [hB] at h1; rw [hA] at h2; linarith
    · intro x hx
      rw [cfCylinder_nil] at hx
      obtain ⟨hx0, hx1⟩ := hx
      rw [hA, hB]
      exact Or.inl ⟨hx0, hx1.le⟩
  | cons t a ih =>
    have ht : 1 ≤ t := ha t (by simp)
    have ha' : ∀ x ∈ a, 1 ≤ x := fun x hx => ha x (by simp [hx])
    obtain ⟨ihA, ihB⟩ := ih ha'
    obtain ⟨hA0, hA1, hB0, hB1, -, -⟩ := endpoint_bounds a ha'
    have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have hAc := endA_cons t a ha'
    have hBc := endB_cons t a ha'
    have hposA : (0:ℝ) < (t : ℝ) + endA a := by linarith
    have hposB : (0:ℝ) < (t : ℝ) + endB a := by linarith
    have hAcpos : (0:ℝ) < endA (t :: a) := by rw [hAc]; positivity
    have hBcpos : (0:ℝ) < endB (t :: a) := by rw [hBc]; positivity
    have hAcle : endA (t :: a) ≤ 1 := by
      rw [hAc]; rw [div_le_one hposA]; linarith
    have hBcle : endB (t :: a) ≤ 1 := by
      rw [hBc]; rw [div_le_one hposB]; linarith
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- endA_cons < x < endB_cons : y between endB and endA
        rw [hAc] at h1; rw [hBc] at h2
        have hxpos : 0 < x := lt_trans (by positivity) h1
        have hξlow : (t : ℝ) + endB a < x⁻¹ := by
          have h := (inv_lt_inv₀ (one_div_pos.mpr hposB) hxpos).mpr h2
          rw [one_div, inv_inv] at h
          exact h
        have hξhigh : x⁻¹ < (t : ℝ) + endA a := by
          have h := (inv_lt_inv₀ hxpos (one_div_pos.mpr hposA)).mpr h1
          rw [one_div, inv_inv] at h
          exact h
        have hfloor : ⌊x⁻¹⌋ = (t : ℤ) := by
          rw [Int.floor_eq_iff]
          constructor
          · exact_mod_cast (le_trans (by linarith : (t:ℝ) ≤ (t:ℝ) + endB a) (le_of_lt hξlow))
          · push_cast; linarith
        have hy : Int.fract x⁻¹ ∈ cfCylinder a := by
          apply ihA
          right
          have hy_eq : Int.fract x⁻¹ = x⁻¹ - (t : ℝ) := by
            rw [Int.fract, hfloor]; push_cast; ring
          rw [hy_eq]
          constructor <;> linarith
        have hleB : 1 / ((t : ℝ) + endB a) ≤ 1 := by rw [div_le_one hposB]; linarith
        have hx1 : x < 1 := lt_of_lt_of_le h2 hleB
        exact cyl_mem_cons hxpos hx1 hfloor hy
      · -- endB_cons < x < endA_cons : y between endA and endB
        rw [hBc] at h1; rw [hAc] at h2
        have hxpos : 0 < x := lt_trans (by positivity) h1
        have hξlow : (t : ℝ) + endA a < x⁻¹ := by
          have h := (inv_lt_inv₀ (one_div_pos.mpr hposA) hxpos).mpr h2
          rw [one_div, inv_inv] at h
          exact h
        have hξhigh : x⁻¹ < (t : ℝ) + endB a := by
          have h := (inv_lt_inv₀ hxpos (one_div_pos.mpr hposB)).mpr h1
          rw [one_div, inv_inv] at h
          exact h
        have hfloor : ⌊x⁻¹⌋ = (t : ℤ) := by
          rw [Int.floor_eq_iff]
          constructor
          · exact_mod_cast (le_trans (by linarith : (t:ℝ) ≤ (t:ℝ) + endA a) (le_of_lt hξlow))
          · push_cast; linarith
        have hy : Int.fract x⁻¹ ∈ cfCylinder a := by
          apply ihA
          left
          have hy_eq : Int.fract x⁻¹ = x⁻¹ - (t : ℝ) := by
            rw [Int.fract, hfloor]; push_cast; ring
          rw [hy_eq]
          constructor <;> linarith
        have hleA : 1 / ((t : ℝ) + endA a) ≤ 1 := by rw [div_le_one hposA]; linarith
        have hx1 : x < 1 := lt_of_lt_of_le h2 hleA
        exact cyl_mem_cons hxpos hx1 hfloor hy
    · intro x hx
      obtain ⟨hxpos, hx1, hfloor, hy⟩ := cyl_of_mem_cons hx
      have hybounds := ihB _ hy
      have hposY : (0:ℝ) < (t : ℝ) + Int.fract x⁻¹ := by
        have hnn := Int.fract_nonneg (x⁻¹)
        linarith
      have hxeq : x = 1 / ((t : ℝ) + Int.fract x⁻¹) := by
        have h1 : (t : ℝ) + Int.fract x⁻¹ = x⁻¹ := by
          rw [Int.fract, hfloor]; push_cast; ring
        rw [h1, one_div, inv_inv]
      rcases hybounds with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- endA <= y <= endB : endB_cons <= x <= endA_cons
        right
        rw [hxeq, hAc, hBc]
        constructor
        · exact one_div_le_one_div_of_le hposY (by linarith)
        · exact one_div_le_one_div_of_le hposA (by linarith)
      · left
        rw [hxeq, hAc, hBc]
        constructor
        · exact one_div_le_one_div_of_le hposY (by linarith)
        · exact one_div_le_one_div_of_le hposB (by linarith)

private theorem convergentMatrix_det (a : List ℕ) :
    (convergentMatrix a).det = (-1 : ℤ) ^ a.length := by
  induction a with
  | nil => simp [convergentMatrix_nil]
  | cons t a ih =>
    rw [convergentMatrix_cons, Matrix.det_mul, ih]
    have hdet : (!![0, 1; 1, (t : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det = -1 := by
      simp [Matrix.det_fin_two]
    rw [hdet]
    simp [List.length_cons, pow_succ]

private theorem fundInterval_mem_of_between {α β x : ℝ}
    (h : (α < x ∧ x < β) ∨ (β < x ∧ x < α)) : x ∈ fundInterval α β := by
  unfold fundInterval
  split_ifs with hlt
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1.le, h2⟩
    · exact absurd (lt_trans h1 h2) (not_lt.mpr hlt.le)
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (lt_trans h1 h2) hlt
    · exact ⟨h1, h2.le⟩

private theorem fundInterval_between {α β x : ℝ} (hx : x ∈ fundInterval α β) :
    (α ≤ x ∧ x ≤ β) ∨ (β ≤ x ∧ x ≤ α) := by
  by_cases hlt : α < β
  · rw [fundInterval_of_lt hlt] at hx
    exact Or.inl ⟨hx.1, hx.2.le⟩
  · have hle : β ≤ α := le_of_not_gt hlt
    have heq : fundInterval α β = Set.Ioc β α := by
      change (if α < β then Set.Ico α β else Set.Ioc β α) = Set.Ioc β α
      exact ite_eq_right (not_lt.mpr hle)
    rw [heq] at hx
    exact Or.inr ⟨hx.1.le, hx.2⟩

private theorem cylinder_ae (b : List ℕ) (hb : ∀ x ∈ b, 1 ≤ x) :
    cfCylinder b =ᵐ[volume] fundInterval (endA b) (endB b) := by
  obtain ⟨hA, hB⟩ := cylinder_between b hb
  rw [ae_eq_set]
  have hfin : (({endA b, endB b} : Set ℝ)).Finite :=
    (Set.finite_singleton (endB b)).insert (endA b)
  have hmeas : volume ({endA b, endB b} : Set ℝ) = 0 := hfin.measure_zero volume
  constructor
  · apply measure_mono_null _ hmeas
    intro x hx
    obtain ⟨hxC, hxF⟩ := hx
    have hbet := hB x hxC
    by_contra hnot
    have hne1 : x ≠ endA b := by intro h; apply hnot; simp [h]
    have hne2 : x ≠ endB b := by intro h; apply hnot; simp [h]
    have hstrict : (endA b < x ∧ x < endB b) ∨ (endB b < x ∧ x < endA b) := by
      rcases hbet with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨lt_of_le_of_ne h1 hne1.symm, lt_of_le_of_ne h2 hne2⟩
      · exact Or.inr ⟨lt_of_le_of_ne h1 hne2.symm, lt_of_le_of_ne h2 hne1⟩
    exact hxF (fundInterval_mem_of_between hstrict)
  · apply measure_mono_null _ hmeas
    intro x hx
    obtain ⟨hxF, hxC⟩ := hx
    by_contra hnot
    have hne1 : x ≠ endA b := by intro h; apply hnot; simp [h]
    have hne2 : x ≠ endB b := by intro h; apply hnot; simp [h]
    have hbet := fundInterval_between hxF
    have hstrict : (endA b < x ∧ x < endB b) ∨ (endB b < x ∧ x < endA b) := by
      rcases hbet with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨lt_of_le_of_ne h1 hne1.symm, lt_of_le_of_ne h2 hne2⟩
      · exact Or.inr ⟨lt_of_le_of_ne h1 hne2.symm, lt_of_le_of_ne h2 hne1⟩
    exact hxC (hA x hstrict)

private theorem endB_eq (b : List ℕ) (hb : ∀ x ∈ b, 1 ≤ x) :
    endB b = endA b + (-1 : ℝ) ^ b.length /
      ((convergentMatrix b 1 1 : ℝ) *
        ((convergentMatrix b 1 1 : ℝ) + (convergentMatrix b 1 0 : ℝ))) := by
  obtain ⟨h00, h01, h10, h11, -, -, -⟩ := entries_pos' b hb
  have hq : (0:ℝ) < (convergentMatrix b 1 1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one h11)
  have hsum : (0:ℝ) < (convergentMatrix b 1 1 : ℝ) + (convergentMatrix b 1 0 : ℝ) := by
    have h10' : (0:ℝ) ≤ (convergentMatrix b 1 0 : ℝ) := by exact_mod_cast h10
    linarith
  have hdet : ((convergentMatrix b).det : ℝ) = (-1 : ℝ) ^ b.length := by
    rw [convergentMatrix_det]; push_cast; ring
  have hdet2 : (convergentMatrix b 0 0 : ℝ) * (convergentMatrix b 1 1 : ℝ) -
      (convergentMatrix b 0 1 : ℝ) * (convergentMatrix b 1 0 : ℝ) = (-1 : ℝ) ^ b.length := by
    have h := hdet
    rw [Matrix.det_fin_two] at h
    push_cast at h
    exact h
  rw [endA, endB]
  field_simp
  nlinarith [hdet2]
  -- fallback: linear combination
  -- ring_nf
  -- linarith [hdet2]

private theorem aux (a : List ℕ) (ha : (∀ x ∈ a, 0 < x))
    (t : ℕ) (ht : 1 ≤ t) :
    cfCylinder a.reverse =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ))
          ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
              ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
              (convergentMatrix a 1 1 : ℝ)))) ∧
      cfCylinder (a ++ [t]) =ᵐ[volume]
        fundInterval (((convergentMatrix a 0 0 : ℝ) + t * (convergentMatrix a 0 1 : ℝ)) /
            ((convergentMatrix a 1 0 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)))
          (((convergentMatrix a 0 0 : ℝ) + t * (convergentMatrix a 0 1 : ℝ)) /
              ((convergentMatrix a 1 0 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)) +
            (-1) ^ (a.length + 1) / (((convergentMatrix a 1 0 : ℝ) + t *
                (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 1 0 : ℝ) + (t + 1) *
                (convergentMatrix a 1 1 : ℝ)))) ∧
      cfCylinder (t :: a) =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 0 1 : ℝ) + t *
            (convergentMatrix a 1 1 : ℝ)))
          ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 0 1 : ℝ) + t *
              (convergentMatrix a 1 1 : ℝ)) +
            (-1) ^ (a.length + 1) / (((convergentMatrix a 0 1 : ℝ) + t *
                (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 0 0 : ℝ) +
                (convergentMatrix a 0 1 : ℝ) + t * ((convergentMatrix a 1 0 : ℝ) +
                (convergentMatrix a 1 1 : ℝ))))) ∧
      cfCylinder (t :: a.reverse) =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 1 0 : ℝ) + t *
            (convergentMatrix a 1 1 : ℝ)))
          ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 1 0 : ℝ) + t *
              (convergentMatrix a 1 1 : ℝ)) +
            (-1) ^ (a.length + 1) / (((convergentMatrix a 1 0 : ℝ) + t *
                (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 0 0 : ℝ) +
                (convergentMatrix a 1 0 : ℝ) + t * ((convergentMatrix a 0 1 : ℝ) +
                (convergentMatrix a 1 1 : ℝ))))) := by
  have hmat := convergentMatrix_reverse_append_cons a ha t ht
  obtain ⟨hm1, hm2, hm3, hm4⟩ := hmat
  have ha1 : ∀ x ∈ a, 1 ≤ x := fun x hx => ha x hx
  have hrev : ∀ x ∈ a.reverse, 1 ≤ x := by
    intro x hx; rw [List.mem_reverse] at hx; exact ha1 x hx
  have happ : ∀ x ∈ a ++ [t], 1 ≤ x := by
    intro x hx; rw [List.mem_append] at hx; rcases hx with hx | hx
    · exact ha1 x hx
    · rw [List.mem_singleton] at hx; subst hx; exact ht
  have hcons : ∀ x ∈ t :: a, 1 ≤ x := by
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact ht
    · exact ha1 x hx
  have hconsr : ∀ x ∈ t :: a.reverse, 1 ≤ x := by
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact ht
    · exact hrev x hx
  -- entry equalities
  have e_rev01 : convergentMatrix a.reverse 0 1 = convergentMatrix a 1 0 := by rw [hm1]; simp
  have e_rev11 : convergentMatrix a.reverse 1 1 = convergentMatrix a 1 1 := by rw [hm1]; simp
  have e_rev10 : convergentMatrix a.reverse 1 0 = convergentMatrix a 0 1 := by rw [hm1]; simp
  have e_app01 : convergentMatrix (a ++ [t]) 0 1 =
      convergentMatrix a 0 0 + t * convergentMatrix a 0 1 := by
    rw [hm2]; simp
  have e_app11 : convergentMatrix (a ++ [t]) 1 1 =
      convergentMatrix a 1 0 + t * convergentMatrix a 1 1 := by
    rw [hm2]; simp
  have e_app10 : convergentMatrix (a ++ [t]) 1 0 = convergentMatrix a 1 1 := by rw [hm2]; simp
  have e_con01 : convergentMatrix (t :: a) 0 1 = convergentMatrix a 1 1 := by rw [hm3]; simp
  have e_con11 : convergentMatrix (t :: a) 1 1 =
      convergentMatrix a 0 1 + t * convergentMatrix a 1 1 := by
    rw [hm3]; simp
  have e_con10 : convergentMatrix (t :: a) 1 0 =
      convergentMatrix a 0 0 + t * convergentMatrix a 1 0 := by
    rw [hm3]; simp
  have e_conr01 : convergentMatrix (t :: a.reverse) 0 1 =
      convergentMatrix a 1 1 := by
    rw [hm4]; simp
  have e_conr11 : convergentMatrix (t :: a.reverse) 1 1 =
      convergentMatrix a 1 0 + t * convergentMatrix a 1 1 := by
    rw [hm4]; simp
  have e_conr10 : convergentMatrix (t :: a.reverse) 1 0 =
      convergentMatrix a 0 0 + t * convergentMatrix a 0 1 := by
    rw [hm4]; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := cylinder_ae a.reverse hrev
    rw [endB_eq a.reverse hrev, endA, e_rev01, e_rev11, e_rev10] at h
    rw [List.length_reverse] at h
    have hdelta : (-1 : ℝ) ^ a.length /
        (((convergentMatrix a 1 1 : ℝ)) *
          ((convergentMatrix a 1 1 : ℝ) + (convergentMatrix a 0 1 : ℝ))) =
        (-1 : ℝ) ^ a.length /
        ((convergentMatrix a 1 1 : ℝ) *
          ((convergentMatrix a 0 1 : ℝ) + (convergentMatrix a 1 1 : ℝ))) := by
      congr 2
      ring
    rw [hdelta] at h
    exact h
  · have h := cylinder_ae (a ++ [t]) happ
    rw [endB_eq (a ++ [t]) happ, endA, e_app01, e_app11, e_app10] at h
    simp only [List.length_append, List.length_singleton] at h
    push_cast at h
    have hdelta : (-1 : ℝ) ^ (a.length + 1) /
        (((convergentMatrix a 1 0 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)) *
          (((convergentMatrix a 1 0 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)) +
            (convergentMatrix a 1 1 : ℝ))) =
        (-1 : ℝ) ^ (a.length + 1) / (((convergentMatrix a 1 0 : ℝ) + t *
            (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 1 0 : ℝ) + (t + 1) *
            (convergentMatrix a 1 1 : ℝ))) := by
      congr 1
      ring
    rw [hdelta] at h
    exact h
  · have h := cylinder_ae (t :: a) hcons
    rw [endB_eq (t :: a) hcons, endA, e_con01, e_con11, e_con10] at h
    simp only [List.length_cons] at h
    push_cast at h
    have hdelta : (-1 : ℝ) ^ (a.length + 1) /
        (((convergentMatrix a 0 1 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)) *
          (((convergentMatrix a 0 1 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)) +
            ((convergentMatrix a 0 0 : ℝ) + t * (convergentMatrix a 1 0 : ℝ)))) =
        (-1 : ℝ) ^ (a.length + 1) / (((convergentMatrix a 0 1 : ℝ) + t *
            (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 0 0 : ℝ) +
            (convergentMatrix a 0 1 : ℝ) + t * ((convergentMatrix a 1 0 : ℝ) +
            (convergentMatrix a 1 1 : ℝ)))) := by
      congr 1
      ring
    rw [hdelta] at h
    exact h
  · have h := cylinder_ae (t :: a.reverse) hconsr
    rw [endB_eq (t :: a.reverse) hconsr, endA, e_conr01, e_conr11, e_conr10] at h
    simp only [List.length_cons, List.length_reverse] at h
    push_cast at h
    have hdelta : (-1 : ℝ) ^ (a.length + 1) /
        (((convergentMatrix a 1 0 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)) *
          (((convergentMatrix a 1 0 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)) +
            ((convergentMatrix a 0 0 : ℝ) + t * (convergentMatrix a 0 1 : ℝ)))) =
        (-1 : ℝ) ^ (a.length + 1) / (((convergentMatrix a 1 0 : ℝ) + t *
            (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 0 0 : ℝ) +
            (convergentMatrix a 1 0 : ℝ) + t * ((convergentMatrix a 0 1 : ℝ) +
            (convergentMatrix a 1 1 : ℝ)))) := by
      congr 1
      ring
    rw [hdelta] at h
    exact h

end cfCylinder_reverse_append_cons_ae_eq

/-- **Fundamental intervals of reversed and extended strings.** Let $a = (a_1, \ldots, a_n)$ be a
finite string of positive integers with convergent matrix
$C(a) = \begin{pmatrix} p' & p \\ q' & q \end{pmatrix}$, let $t \ge 1$ be an integer, write
$\overleftarrow{a} = (a_n, \ldots, a_1)$ for the reversed string, and for real numbers $x$ and $y$
let $\langle x, y \rangle$ be $[x, y)$ if $x < y$ and $(y, x]$ otherwise. Write $I(b)$ for the
fundamental interval of a string $b$, and set $u = (p' + tp)/(q' + tq)$, $v = q/(p + tq)$ and
$w = q/(q' + tq)$. Then each of the following equalities holds up to a set of Lebesgue measure
zero:
(i) $I(\overleftarrow{a}) = \langle q'/q, \; q'/q + (-1)^n / (q(p + q)) \rangle$;
(ii) $I(a_1, \ldots, a_n, t) = \langle u, \; u + (-1)^{n+1} / ((q' + tq)(q' + (t + 1)q)) \rangle$;
(iii) $I(t, a_1, \ldots, a_n) = \langle v, \; v + (-1)^{n+1} / ((p + tq)(p' + p + t(q' + q)))
\rangle$;
(iv) $I(t, a_n, \ldots, a_1) = \langle w, \; w + (-1)^{n+1} / ((q' + tq)(p' + q' + t(p + q)))
\rangle$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 2.4 (`integers-2025-A89-lem-2-4`). -/
theorem cfCylinder_reverse_append_cons_ae_eq (a : List ℕ) (ha : (∀ x ∈ a, 0 < x))
    (t : ℕ) (ht : 1 ≤ t) :
    cfCylinder a.reverse =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ))
          ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
              ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
              (convergentMatrix a 1 1 : ℝ)))) ∧
      cfCylinder (a ++ [t]) =ᵐ[volume]
        fundInterval (((convergentMatrix a 0 0 : ℝ) + t * (convergentMatrix a 0 1 : ℝ)) /
            ((convergentMatrix a 1 0 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)))
          (((convergentMatrix a 0 0 : ℝ) + t * (convergentMatrix a 0 1 : ℝ)) /
              ((convergentMatrix a 1 0 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)) +
            (-1) ^ (a.length + 1) / (((convergentMatrix a 1 0 : ℝ) + t *
                (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 1 0 : ℝ) + (t + 1) *
                (convergentMatrix a 1 1 : ℝ)))) ∧
      cfCylinder (t :: a) =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 0 1 : ℝ) + t *
            (convergentMatrix a 1 1 : ℝ)))
          ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 0 1 : ℝ) + t *
              (convergentMatrix a 1 1 : ℝ)) +
            (-1) ^ (a.length + 1) / (((convergentMatrix a 0 1 : ℝ) + t *
                (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 0 0 : ℝ) +
                (convergentMatrix a 0 1 : ℝ) + t * ((convergentMatrix a 1 0 : ℝ) +
                (convergentMatrix a 1 1 : ℝ))))) ∧
      cfCylinder (t :: a.reverse) =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 1 0 : ℝ) + t *
            (convergentMatrix a 1 1 : ℝ)))
          ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 1 0 : ℝ) + t *
              (convergentMatrix a 1 1 : ℝ)) +
            (-1) ^ (a.length + 1) / (((convergentMatrix a 1 0 : ℝ) + t *
                (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 0 0 : ℝ) +
                (convergentMatrix a 1 0 : ℝ) + t * ((convergentMatrix a 0 1 : ℝ) +
                (convergentMatrix a 1 1 : ℝ))))) :=
  cfCylinder_reverse_append_cons_ae_eq.aux a ha t ht

end

end MetaMathlibExt
