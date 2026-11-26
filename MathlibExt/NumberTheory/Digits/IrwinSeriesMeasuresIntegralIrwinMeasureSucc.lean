/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Analysis.Series.RiemannRearrangement
public import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasures
public import MathlibExt.NumberTheory.Digits.IrwinSeriesLeadingIntegral
public import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasuresLocalMass
public import MathlibExt.NumberTheory.Digits.OrdinaryMomentRecurrence
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Digit decomposition of the Irwin measures, positive index

This module proves that the integral of a bounded measurable function against an Irwin measure
of positive index decomposes over the first base-`b` digit: scaling the variable by `b` peels
off the leading digit, giving the same-index integrals for the digits other than `d` plus the
predecessor-index integral for `d` itself.

Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
Article A11, Lemma 1.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators ENNReal
open Filter MeasureTheory Set

namespace integralIrwinMeasureSucc

/-- The fold defining `stringValue` distributes over the initial accumulator. -/
private theorem foldl_stringValue (b : ℕ) :
    ∀ (Z : List (Fin b)) (m : ℕ),
      Z.foldl (fun n a => b * n + a.val) m =
        m * b ^ Z.length + Z.foldl (fun n a => b * n + a.val) 0 := by
  intro Z
  induction Z with
  | nil => intro m; simp
  | cons a Z ih =>
    intro m
    simp only [List.length_cons, List.foldl_cons, pow_succ', mul_zero, zero_add]
    rw [ih (b * m + a.val), ih a.val]
    ring

/-- The value of a digit string with a given first digit splits into the first
digit's contribution plus the value of the remaining string. -/
private theorem stringValue_cons (b : ℕ) (a : Fin b) (X : List (Fin b)) :
    stringValue b (a :: X) = a.val * b ^ X.length + stringValue b X := by
  unfold stringValue
  simp only [List.foldl_cons]
  rw [foldl_stringValue]
  simp

/-- The value of a digit string is strictly below the place value of its
length. -/
private theorem stringValue_lt (b : ℕ) (X : List (Fin b)) :
    stringValue b X < b ^ X.length := by
  induction X with
  | nil => simp [stringValue]
  | cons a X ih =>
    rw [stringValue_cons]
    have ha : a.val < b := a.isLt
    have h1 : a.val * b ^ X.length + stringValue b X < (a.val + 1) * b ^ X.length := by
      have e : (a.val + 1) * b ^ X.length = a.val * b ^ X.length + b ^ X.length := by
        rw [add_mul, one_mul]
      omega
    have h2 : (a.val + 1) * b ^ X.length ≤ b * b ^ X.length :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ha)
    calc a.val * b ^ X.length + stringValue b X
        < (a.val + 1) * b ^ X.length := h1
      _ ≤ b * b ^ X.length := h2
      _ = b ^ (X.length + 1) := by rw [pow_succ']
      _ = b ^ (a :: X).length := rfl

/-- Every digit-string atom lies in `[0, 1)`. -/
private theorem normalized_mem_Ico (b : ℕ) (hb : 1 < b) (X : List (Fin b)) :
    normalizedStringValue b X ∈ Set.Ico (0 : ℝ) 1 := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hb
  have hB : (0 : ℝ) < (b : ℝ) ^ X.length := pow_pos hbR _
  constructor
  · unfold normalizedStringValue
    exact div_nonneg (Nat.cast_nonneg _) hB.le
  · unfold normalizedStringValue
    rw [div_lt_one hB]
    exact_mod_cast stringValue_lt b X

private noncomputable def phi (b d : ℕ) (hd : d < b) (X : List (Fin b)) : ℝ :=
  (b : ℝ) ^ (-(X.length : ℤ)) * (1 / 2 : ℝ) ^ (X.count ⟨d, hd⟩)

private noncomputable def wt (b d : ℕ) (hd : d < b) (a : Fin b) : ℝ :=
  if a = ⟨d, hd⟩ then (1 / 2 : ℝ) / b else 1 / (b : ℝ)

private theorem phi_nonneg (b d : ℕ) (hd : d < b) (X : List (Fin b)) :
    0 ≤ phi b d hd X := by
  unfold phi
  positivity

private theorem phi_nil (b d : ℕ) (hd : d < b) : phi b d hd [] = 1 := by
  simp [phi]

private theorem phi_cons (b d : ℕ) (hb : 1 < b) (hd : d < b) (a : Fin b)
    (X : List (Fin b)) : phi b d hd (a :: X) = wt b d hd a * phi b d hd X := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hcount : (a :: X).count ⟨d, hd⟩ =
      X.count ⟨d, hd⟩ + (if a = ⟨d, hd⟩ then 1 else 0) := by
    by_cases ha : a = ⟨d, hd⟩
    · subst ha
      rw [List.count_cons_self]
      simp
    · rw [List.count_cons_of_ne ha]
      simp [ha]
  unfold phi wt
  simp only [List.length_cons, hcount]
  have hpow : (b : ℝ) ^ (-((X.length + 1 : ℕ) : ℤ)) =
      (b : ℝ) ^ (-(X.length : ℤ)) * (b : ℝ)⁻¹ := by
    have h : (-((X.length + 1 : ℕ) : ℤ)) = (-(X.length : ℤ)) + (-1 : ℤ) := by
      push_cast; ring
    rw [h, zpow_add₀ hbR, zpow_neg_one]
  rw [hpow]
  split_ifs with ha
  · rw [pow_add, pow_one]
    field_simp
  · simp only [add_zero]
    rw [one_div]
    ring

private theorem sum_wt (b d : ℕ) (hb : 1 < b) (hd : d < b) :
    ∑ a : Fin b, wt b d hd a = ((b : ℝ) - 1 / 2) / b := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have h := (Finset.add_sum_erase Finset.univ (fun a => wt b d hd a)
    (Finset.mem_univ (⟨d, hd⟩ : Fin b))).symm
  have herase : ∑ a ∈ Finset.univ.erase (⟨d, hd⟩ : Fin b), wt b d hd a = ((b : ℝ) - 1) / b := by
    have h1 : ∑ a ∈ Finset.univ.erase (⟨d, hd⟩ : Fin b), wt b d hd a =
        ∑ a ∈ Finset.univ.erase (⟨d, hd⟩ : Fin b), (1 / (b : ℝ)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hane : a ≠ ⟨d, hd⟩ := by
        intro hEq
        exact (Finset.mem_erase.mp ha).1 hEq
      simp [wt, hane]
    rw [h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (⟨d, hd⟩ : Fin b)),
      Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ b)]
    push_cast
    ring
  rw [h, herase]
  simp [wt]
  field_simp
  ring

private theorem phi_bound : ∀ (T : ℕ) (b d : ℕ) (_hb : 1 < b) (hd : d < b)
    (F : Finset (List (Fin b))), (∀ X ∈ F, X.length ≤ T) →
    ∑ X ∈ F, phi b d hd X ≤
      ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t := by
  intro T
  induction T with
  | zero =>
    intro b d _hb hd F hF
    have hsub : F ⊆ {[]} := by
      intro X hX
      have hlen := hF X hX
      simp only [Finset.mem_singleton]
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun X _ _ => phi_nonneg b d hd X)
    rw [Finset.sum_singleton, phi_nil] at hle
    simpa using hle
  | succ T ih =>
    intro b d _hb hd F hF
    have hq : ((b : ℝ) - 1 / 2) / b = ∑ a : Fin b, wt b d hd a := (sum_wt b d _hb hd).symm
    set F0 := F.filter (fun X => X = []) with hF0
    set F1 := F.filter (fun X => ¬ X = []) with hF1
    have hsplit := Finset.sum_filter_add_sum_filter_not F (fun X => X = [])
      (phi b d hd)
    have hF0le : ∑ X ∈ F0, phi b d hd X ≤ 1 := by
      have hsub : F0 ⊆ {[]} := by
        intro X hX
        simp only [hF0, Finset.mem_filter, Finset.mem_singleton] at hX ⊢
        exact hX.2
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun X _ _ => phi_nonneg b d hd X)
      rwa [Finset.sum_singleton, phi_nil] at hle
    have hF1le : ∑ X ∈ F1, phi b d hd X ≤
        (((b : ℝ) - 1 / 2) / b) *
          ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t := by
      set tails := F1.image List.tail with htails
      have hTails : ∀ Y ∈ tails, Y.length ≤ T := by
        intro Y hY
        obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hY
        have hlen := hF X (Finset.mem_of_mem_filter X hX)
        have hne : X ≠ [] := (Finset.mem_filter.mp hX).2
        have htl : X.tail.length = X.length - 1 := by simp [List.length_tail]
        omega
      have hIH := ih b d _hb hd tails hTails
      set P := (Finset.univ ×ˢ tails).filter (fun p : Fin b × List (Fin b) =>
        p.1 :: p.2 ∈ F1) with hP
      have himg : P.image (fun p : Fin b × List (Fin b) => p.1 :: p.2) = F1 := by
        ext X
        constructor
        · intro hX
          obtain ⟨p, hp, hpX⟩ := Finset.mem_image.mp hX
          rw [← hpX]
          exact (Finset.mem_filter.mp hp).2
        · intro hX
          have hne : X ≠ [] := (Finset.mem_filter.mp hX).2
          refine Finset.mem_image.mpr ⟨⟨X.head hne, X.tail⟩, ?_, List.cons_head_tail hne⟩
          apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_product.mpr
            exact ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨X, hX, rfl⟩⟩
          · rw [List.cons_head_tail hne]
            exact hX
      have hF1eq : ∑ X ∈ F1, phi b d hd X =
          ∑ p ∈ P, phi b d hd (p.1 :: p.2) := by
        rw [← himg]
        rw [Finset.sum_image]
        intro p _ q _ hpq
        exact Prod.ext (List.cons.inj hpq).1 (List.cons.inj hpq).2
      have hPle : ∑ p ∈ P, phi b d hd (p.1 :: p.2) ≤
          ∑ p ∈ Finset.univ ×ˢ tails, wt b d hd p.1 * phi b d hd p.2 := by
        have h1 : ∑ p ∈ P, phi b d hd (p.1 :: p.2) ≤
            ∑ p ∈ Finset.univ ×ˢ tails, phi b d hd (p.1 :: p.2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun p _ _ => phi_nonneg b d hd (p.1 :: p.2))
        have h2 : ∑ p ∈ Finset.univ ×ˢ tails, phi b d hd (p.1 :: p.2) =
            ∑ p ∈ Finset.univ ×ˢ tails, wt b d hd p.1 * phi b d hd p.2 := by
          apply Finset.sum_congr rfl
          intro p _
          rw [phi_cons b d _hb hd p.1 p.2]
        exact h1.trans_eq h2
      have hprod : ∑ p ∈ Finset.univ ×ˢ tails, wt b d hd p.1 * phi b d hd p.2 =
          (∑ a : Fin b, wt b d hd a) * ∑ Y ∈ tails, phi b d hd Y := by
        rw [Finset.sum_product, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
      rw [hF1eq]
      rw [hprod] at hPle
      have hwt : 0 ≤ ∑ a : Fin b, wt b d hd a := by
        apply Finset.sum_nonneg
        intro a _
        unfold wt
        split_ifs <;> positivity
      calc ∑ p ∈ P, phi b d hd (p.1 :: p.2)
          ≤ (∑ a : Fin b, wt b d hd a) * ∑ Y ∈ tails, phi b d hd Y := hPle
        _ ≤ (∑ a : Fin b, wt b d hd a) *
            ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t :=
          mul_le_mul_of_nonneg_left hIH hwt
        _ = (((b : ℝ) - 1 / 2) / b) *
            ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t := by
          rw [hq]
    have htot : ∑ X ∈ F, phi b d hd X ≤
        1 + (((b : ℝ) - 1 / 2) / b) *
          ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t := by
      have h := hsplit
      rw [← h]
      linarith [hF0le, hF1le]
    have hgeom : 1 + (((b : ℝ) - 1 / 2) / b) *
          ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t =
        ∑ t ∈ Finset.range (T + 2), (((b : ℝ) - 1 / 2) / b) ^ t := by
      conv_rhs => rw [Finset.sum_range_succ', pow_zero, add_comm]
      rw [Finset.mul_sum]
      apply congrArg (1 + ·)
      apply Finset.sum_congr rfl
      intro t _
      rw [pow_succ]
      ring
    rw [hgeom] at htot
    exact htot

private theorem summable_stringWeight (b d k : ℕ) (hb : 1 < b) (hd : d < b) :
    Summable (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
      (stringWeight b X.1).toReal) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast Nat.zero_lt_of_lt hb
  have hq0 : (0 : ℝ) ≤ ((b : ℝ) - 1 / 2) / b := by
    apply div_nonneg _ hbR.le
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hq1 : ((b : ℝ) - 1 / 2) / b < 1 := by
    rw [div_lt_one hbR]
    linarith
  have hgeom : Summable (fun t : ℕ => (((b : ℝ) - 1 / 2) / b) ^ t) :=
    summable_geometric_of_lt_one hq0 hq1
  have htsum : ∑' t : ℕ, (((b : ℝ) - 1 / 2) / b) ^ t = 2 * (b : ℝ) := by
    rw [tsum_geometric_of_lt_one hq0 hq1]
    have h1 : (1 : ℝ) - ((b : ℝ) - 1 / 2) / b = (1 / 2) / b := by
      field_simp
      ring
    rw [h1, inv_div]
    field_simp
  apply summable_of_sum_le (f := fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
    (stringWeight b X.1).toReal) (c := (2 : ℝ) ^ k * (2 * b))
  · intro X
    exact ENNReal.toReal_nonneg
  · intro U
    set F := U.image (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} => X.1) with hF
    have hsumU : ∑ X ∈ U, (stringWeight b X.1).toReal =
        ∑ X ∈ F, (stringWeight b X).toReal := by
      rw [hF]
      exact (Finset.sum_image (s := U)
        (g := fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} => X.1)
        (f := fun X : List (Fin b) => (stringWeight b X).toReal)
        (fun X _ Y _ hXY => Subtype.ext hXY)).symm
    rw [hsumU]
    have hterm : ∀ X ∈ F, (stringWeight b X).toReal =
        (2 : ℝ) ^ k * phi b d hd X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
      unfold stringWeight phi
      rw [ENNReal.toReal_ofReal (zpow_nonneg (Nat.cast_nonneg b) _), Y.2]
      have h2 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
        rw [← mul_pow]
        norm_num
      calc (b : ℝ) ^ (-(Y.1.length : ℤ))
          = (b : ℝ) ^ (-(Y.1.length : ℤ)) * ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) := by
            rw [h2, mul_one]
        _ = (2 : ℝ) ^ k * ((b : ℝ) ^ (-(Y.1.length : ℤ)) * (1 / 2 : ℝ) ^ k) := by
            ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    set T := F.sup List.length with hT
    have hlen : ∀ X ∈ F, X.length ≤ T := fun X hX => Finset.le_sup hX
    have hbound := phi_bound T b d hb hd F hlen
    have hle1 : (2 : ℝ) ^ k * ∑ X ∈ F, phi b d hd X ≤
        (2 : ℝ) ^ k * ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    have hle2 : ∑ t ∈ Finset.range (T + 1), (((b : ℝ) - 1 / 2) / b) ^ t ≤
        ∑' t : ℕ, (((b : ℝ) - 1 / 2) / b) ^ t :=
      hgeom.sum_le_tsum _ (fun t _ => by positivity)
    rw [htsum] at hle2
    have h2k : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    calc (2 : ℝ) ^ k * ∑ X ∈ F, phi b d hd X
        ≤ (2 : ℝ) ^ k * (2 * (b : ℝ)) :=
          hle1.trans (mul_le_mul_of_nonneg_left hle2 h2k)
      _ = (2 : ℝ) ^ k * (2 * (b : ℝ)) := rfl

/-- Scaling `[0, 1)` by the base lands in `[0, b)`. -/
private theorem mul_mem_Ico (b : ℕ) (hb : 1 < b) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    (b : ℝ) * x ∈ Set.Ico (0 : ℝ) (b : ℝ) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hb
  constructor
  · exact mul_nonneg hbR.le hx0
  · calc (b : ℝ) * x < (b : ℝ) * 1 := mul_lt_mul_of_pos_left hx1 hbR
      _ = (b : ℝ) := mul_one _

/-- Translating `[0, 1)` by a digit lands in `[0, b)`. -/
private theorem add_mem_Ico (b : ℕ) (c : ℕ) (hc : c < b) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    (c : ℝ) + x ∈ Set.Ico (0 : ℝ) (b : ℝ) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have hcb : (c : ℝ) + 1 ≤ (b : ℝ) := by
    have h : c + 1 ≤ b := by omega
    exact_mod_cast h
  constructor
  · exact add_nonneg hc0 hx0
  · calc (c : ℝ) + x < (c : ℝ) + 1 := by linarith
      _ ≤ (b : ℝ) := hcb

/-- Summability transfers along pointwise equalities. -/
private theorem summable_congr {ι : Type*} {f g : ι → ℝ} (hf : Summable f)
    (h : ∀ x, g x = f x) : Summable g :=
  (hf.hasSum.congr_fun h).summable

/-- Weighted sums over digit strings are summable for bounded integrands. -/
private theorem summable_weight_mul (b d : ℕ) (hb : 1 < b) (hd : d < b)
    (g : ℝ → ℝ) (C : ℝ) (hC : ∀ x ∈ Set.Ico (0 : ℝ) 1, ‖g x‖ ≤ C)
    (j : ℕ) :
    Summable (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = j} =>
      (stringWeight b X.1).toReal * g (normalizedStringValue b X.1)) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun X => norm_nonneg _)
    (fun X => ?_) ((summable_stringWeight b d j hb hd).mul_left C)
  calc ‖(stringWeight b X.1).toReal * g (normalizedStringValue b X.1)‖
      = (stringWeight b X.1).toReal * ‖g (normalizedStringValue b X.1)‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ (stringWeight b X.1).toReal * C :=
        mul_le_mul_of_nonneg_left (hC _ (normalized_mem_Ico b hb X.1))
          ENNReal.toReal_nonneg
    _ = C * (stringWeight b X.1).toReal := mul_comm _ _

/-- Integrals against an Irwin measure are sums over the digit strings. -/
private theorem integral_eq_tsum (b d : ℕ) (hb : 1 < b) (hd : d < b)
    (g : ℝ → ℝ) (C : ℝ) (hC : ∀ x ∈ Set.Ico (0 : ℝ) 1, ‖g x‖ ≤ C)
    (j : ℕ) :
    ∫ x in Set.Ico (0 : ℝ) 1, g x ∂irwinMeasure b d j hd =
      ∑' X : {X : List (Fin b) // X.count ⟨d, hd⟩ = j},
        (stringWeight b X.1).toReal * g (normalizedStringValue b X.1) := by
  have hmem : ∀ X : {X : List (Fin b) // X.count ⟨d, hd⟩ = j},
      normalizedStringValue b X.1 ∈ Set.Ico (0 : ℝ) 1 :=
    fun X => normalized_mem_Ico b hb X.1
  have hsumm : Summable (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = j} =>
      (stringWeight b X.1).toReal *
        ‖Set.indicator (Set.Ico (0 : ℝ) 1) g (normalizedStringValue b X.1)‖) := by
    refine Summable.of_nonneg_of_le
      (fun X => mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _))
      (fun X => ?_) ((summable_stringWeight b d j hb hd).mul_left C)
    rw [Set.indicator_of_mem (hmem X) g]
    calc (stringWeight b X.1).toReal * ‖g (normalizedStringValue b X.1)‖
        ≤ (stringWeight b X.1).toReal * C :=
          mul_le_mul_of_nonneg_left (hC _ (hmem X)) ENNReal.toReal_nonneg
      _ = C * (stringWeight b X.1).toReal := mul_comm _ _
  have hc : ∀ X : {X : List (Fin b) // X.count ⟨d, hd⟩ = j},
      stringWeight b X.1 ≠ ∞ :=
    fun X => ENNReal.ofReal_ne_top
  rw [← MeasureTheory.integral_indicator measurableSet_Ico]
  simp only [irwinMeasure, stringAtom]
  rw [MeasureTheory.integral_sum_dirac_eq_tsum hc hsumm]
  refine tsum_congr fun X => ?_
  rw [Set.indicator_of_mem (hmem X) g, smul_eq_mul]

/-- The weight of a nonempty digit string factors off one power of the base. -/
private theorem weight_cons_toReal (b : ℕ) (hb : 1 < b) (a : Fin b)
    (Y : List (Fin b)) :
    (stringWeight b (a :: Y)).toReal
      = (1 / (b : ℝ)) * (stringWeight b Y).toReal := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hlen : (((a :: Y).length : ℕ) : ℤ) = (Y.length : ℤ) + 1 := by
    simp [List.length_cons]
  have e : (b : ℝ) ^ (-(((a :: Y).length : ℕ) : ℤ))
      = (1 / (b : ℝ)) * (b : ℝ) ^ (-(Y.length : ℤ)) := by
    rw [hlen, show (-((Y.length : ℤ) + 1)) = (-(Y.length : ℤ)) + (-1 : ℤ) by ring,
      zpow_add₀ hbR, zpow_neg_one, one_div, mul_comm]
  unfold stringWeight
  rw [ENNReal.toReal_ofReal (zpow_nonneg (Nat.cast_nonneg b) _),
    ENNReal.toReal_ofReal (zpow_nonneg (Nat.cast_nonneg b) _)]
  exact e

/-- Scaling a digit-string atom by the base peels off the first digit. -/
private theorem atom_cons (b : ℕ) (hb : 1 < b) (a : Fin b) (Y : List (Fin b)) :
    (b : ℝ) * normalizedStringValue b (a :: Y)
      = (a.val : ℝ) + normalizedStringValue b Y := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hb
  have hbRne : (b : ℝ) ≠ 0 := ne_of_gt hbR
  have hBne : (b : ℝ) ^ Y.length ≠ 0 := pow_ne_zero _ hbRne
  have hval : stringValue b (a :: Y) = a.val * b ^ Y.length + stringValue b Y :=
    stringValue_cons b a Y
  unfold normalizedStringValue
  rw [hval]
  simp only [List.length_cons, pow_succ']
  push_cast
  field_simp

/-- Digit strings with positive count split by their first digit. -/
private def consEquiv (b d k : ℕ) (hd : d < b) (hk : 1 ≤ k) :
    {X : List (Fin b) // X.count ⟨d, hd⟩ = k} ≃
      Σ a : Fin b, {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k} where
  toFun X :=
    ⟨X.1.head (by intro h; have h2 := X.2; rw [h] at h2; simp at h2; omega),
      ⟨X.1.tail, by rw [List.cons_head_tail]; exact X.2⟩⟩
  invFun p := ⟨p.1 :: p.2.1, p.2.2⟩
  left_inv X := Subtype.ext (List.cons_head_tail _)
  right_inv p := by obtain ⟨a, Y⟩ := p; rfl

/-- The fiber over the digit `d` sums over strings of predecessor count. -/
private theorem fiber_pred_eq (b d : ℕ) (hd : d < b) (k : ℕ) (hk : 1 ≤ k) :
    (fun Y : List (Fin b) => (⟨d, hd⟩ :: Y).count ⟨d, hd⟩ = k)
      = fun Y => Y.count ⟨d, hd⟩ = k - 1 := by
  funext Y
  exact propext ⟨fun h => by rw [List.count_cons_self] at h; omega,
    fun h => by rw [List.count_cons_self]; omega⟩

/-- The fiber over a digit other than `d` keeps the same count. -/
private theorem fiber_same_eq (b d : ℕ) (hd : d < b) (k : ℕ) (a : Fin b)
    (ha : a ≠ ⟨d, hd⟩) :
    (fun Y : List (Fin b) => (a :: Y).count ⟨d, hd⟩ = k)
      = fun Y => Y.count ⟨d, hd⟩ = k := by
  funext Y
  exact propext ⟨fun h => by rw [List.count_cons_of_ne ha] at h; exact h,
    fun h => by rw [List.count_cons_of_ne ha]; exact h⟩

/-- Summability of the fiber over the digit `d`. -/
private theorem fiber_summable_of_eq (b d : ℕ) (hb : 1 < b) (hd : d < b)
    (f : ℝ → ℝ) (C : ℝ) (hC : ∀ y ∈ Set.Ico (0 : ℝ) (b : ℝ), ‖f y‖ ≤ C)
    (k : ℕ) (hk : 1 ≤ k) (a : Fin b) (ha : a = ⟨d, hd⟩) :
    Summable (fun Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k} =>
      (stringWeight b (a :: Y.1)).toReal
        * f ((b : ℝ) * normalizedStringValue b (a :: Y.1))) := by
  subst ha
  let σ : {Y : List (Fin b) // (⟨d, hd⟩ :: Y).count ⟨d, hd⟩ = k} ≃
      {Y : List (Fin b) // Y.count ⟨d, hd⟩ = k - 1} :=
    Equiv.subtypeEquivProp (fiber_pred_eq b d hd k hk)
  have hS : Summable (fun Z : {Y : List (Fin b) // Y.count ⟨d, hd⟩ = k - 1} =>
      (stringWeight b Z.1).toReal * f ((d : ℝ) + normalizedStringValue b Z.1)) :=
    summable_weight_mul b d hb hd (fun x => f ((d : ℝ) + x)) C
      (fun x hx => hC ((d : ℝ) + x) (add_mem_Ico b d hd x hx)) (k - 1)
  have hT : Summable (fun Y : {Y : List (Fin b) // (⟨d, hd⟩ :: Y).count ⟨d, hd⟩ = k} =>
      (stringWeight b Y.1).toReal * f ((d : ℝ) + normalizedStringValue b Y.1)) :=
    summable_congr ((σ.summable_iff).mpr hS) (fun Y => rfl)
  have hmul : Summable (fun Y : {Y : List (Fin b) // (⟨d, hd⟩ :: Y).count ⟨d, hd⟩ = k} =>
      (1 / (b : ℝ))
        * ((stringWeight b Y.1).toReal * f ((d : ℝ) + normalizedStringValue b Y.1))) :=
    hT.mul_left _
  refine summable_congr hmul (fun Y => ?_)
  have hat : (b : ℝ) * normalizedStringValue b (⟨d, hd⟩ :: Y.1)
      = (d : ℝ) + normalizedStringValue b Y.1 :=
    atom_cons b hb _ _
  rw [weight_cons_toReal b hb _ _, hat]
  ring

/-- Summability of the fiber over a digit other than `d`. -/
private theorem fiber_summable_of_ne (b d : ℕ) (hb : 1 < b) (hd : d < b)
    (f : ℝ → ℝ) (C : ℝ) (hC : ∀ y ∈ Set.Ico (0 : ℝ) (b : ℝ), ‖f y‖ ≤ C)
    (k : ℕ) (a : Fin b) (ha : a ≠ ⟨d, hd⟩) :
    Summable (fun Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k} =>
      (stringWeight b (a :: Y.1)).toReal
        * f ((b : ℝ) * normalizedStringValue b (a :: Y.1))) := by
  let σ : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k} ≃
      {Y : List (Fin b) // Y.count ⟨d, hd⟩ = k} :=
    Equiv.subtypeEquivProp (fiber_same_eq b d hd k a ha)
  have hS : Summable (fun Z : {Y : List (Fin b) // Y.count ⟨d, hd⟩ = k} =>
      (stringWeight b Z.1).toReal * f ((a.val : ℝ) + normalizedStringValue b Z.1)) :=
    summable_weight_mul b d hb hd (fun x => f ((a.val : ℝ) + x)) C
      (fun x hx => hC ((a.val : ℝ) + x) (add_mem_Ico b a.val a.isLt x hx))
      k
  have hT : Summable (fun Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k} =>
      (stringWeight b Y.1).toReal * f ((a.val : ℝ) + normalizedStringValue b Y.1)) :=
    summable_congr ((σ.summable_iff).mpr hS) (fun Y => rfl)
  have hmul : Summable (fun Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k} =>
      (1 / (b : ℝ))
        * ((stringWeight b Y.1).toReal * f ((a.val : ℝ) + normalizedStringValue b Y.1))) :=
    hT.mul_left _
  refine summable_congr hmul (fun Y => ?_)
  have hat : (b : ℝ) * normalizedStringValue b (a :: Y.1)
      = (a.val : ℝ) + normalizedStringValue b Y.1 :=
    atom_cons b hb _ _
  rw [weight_cons_toReal b hb _ _, hat]
  ring

/-- Value of the fiber sum over the digit `d`. -/
private theorem fiber_tsum_of_eq (b d : ℕ) (hb : 1 < b) (hd : d < b)
    (f : ℝ → ℝ) (C : ℝ) (hC : ∀ y ∈ Set.Ico (0 : ℝ) (b : ℝ), ‖f y‖ ≤ C)
    (k : ℕ) (hk : 1 ≤ k) (a : Fin b) (ha : a = ⟨d, hd⟩) :
    (∑' Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
      (stringWeight b (a :: Y.1)).toReal
        * f ((b : ℝ) * normalizedStringValue b (a :: Y.1)))
    = (1 / (b : ℝ))
      * ∫ x in Set.Ico (0 : ℝ) 1, f ((d : ℝ) + x) ∂irwinMeasure b d (k - 1) hd := by
  subst ha
  have hterm : ∀ Y : {Y : List (Fin b) // (⟨d, hd⟩ :: Y).count ⟨d, hd⟩ = k},
      (stringWeight b (⟨d, hd⟩ :: Y.1)).toReal
          * f ((b : ℝ) * normalizedStringValue b (⟨d, hd⟩ :: Y.1))
        = (1 / (b : ℝ))
          * ((stringWeight b Y.1).toReal * f ((d : ℝ) + normalizedStringValue b Y.1)) := by
    intro Y
    have hat : (b : ℝ) * normalizedStringValue b (⟨d, hd⟩ :: Y.1)
        = (d : ℝ) + normalizedStringValue b Y.1 :=
      atom_cons b hb _ _
    rw [weight_cons_toReal b hb _ _, hat]
    ring
  let σ : {Y : List (Fin b) // (⟨d, hd⟩ :: Y).count ⟨d, hd⟩ = k} ≃
      {Y : List (Fin b) // Y.count ⟨d, hd⟩ = k - 1} :=
    Equiv.subtypeEquivProp (fiber_pred_eq b d hd k hk)
  calc (∑' Y : {Y : List (Fin b) // (⟨d, hd⟩ :: Y).count ⟨d, hd⟩ = k},
          (stringWeight b (⟨d, hd⟩ :: Y.1)).toReal
            * f ((b : ℝ) * normalizedStringValue b (⟨d, hd⟩ :: Y.1)))
      = ∑' Y : {Y : List (Fin b) // (⟨d, hd⟩ :: Y).count ⟨d, hd⟩ = k},
          (1 / (b : ℝ))
            * ((stringWeight b Y.1).toReal * f ((d : ℝ) + normalizedStringValue b Y.1)) :=
        tsum_congr hterm
    _ = (1 / (b : ℝ)) * ∑' Y : {Y : List (Fin b) // (⟨d, hd⟩ :: Y).count ⟨d, hd⟩ = k},
          ((stringWeight b Y.1).toReal * f ((d : ℝ) + normalizedStringValue b Y.1)) :=
        tsum_mul_left
    _ = (1 / (b : ℝ)) * ∑' Z : {Z : List (Fin b) // Z.count ⟨d, hd⟩ = k - 1},
          ((stringWeight b Z.1).toReal * f ((d : ℝ) + normalizedStringValue b Z.1)) := by
        congr 1
        rw [← σ.tsum_eq (fun Z : {Z : List (Fin b) // Z.count ⟨d, hd⟩ = k - 1} =>
          ((stringWeight b Z.1).toReal * f ((d : ℝ) + normalizedStringValue b Z.1)))]
        refine tsum_congr fun Y => rfl
    _ = (1 / (b : ℝ))
          * ∫ x in Set.Ico (0 : ℝ) 1, f ((d : ℝ) + x) ∂irwinMeasure b d (k - 1) hd := by
        congr 1
        exact (integral_eq_tsum b d hb hd (fun x => f ((d : ℝ) + x)) C
          (fun x hx => hC ((d : ℝ) + x) (add_mem_Ico b d hd x hx)) (k - 1)).symm

/-- Value of the fiber sum over a digit other than `d`. -/
private theorem fiber_tsum_of_ne (b d : ℕ) (hb : 1 < b) (hd : d < b)
    (f : ℝ → ℝ) (C : ℝ) (hC : ∀ y ∈ Set.Ico (0 : ℝ) (b : ℝ), ‖f y‖ ≤ C)
    (k : ℕ) (a : Fin b) (ha : a ≠ ⟨d, hd⟩) :
    (∑' Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
      (stringWeight b (a :: Y.1)).toReal
        * f ((b : ℝ) * normalizedStringValue b (a :: Y.1)))
    = (1 / (b : ℝ))
      * ∫ x in Set.Ico (0 : ℝ) 1, f ((a.val : ℝ) + x) ∂irwinMeasure b d k hd := by
  have hterm : ∀ Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
      (stringWeight b (a :: Y.1)).toReal
          * f ((b : ℝ) * normalizedStringValue b (a :: Y.1))
        = (1 / (b : ℝ))
          * ((stringWeight b Y.1).toReal
            * f ((a.val : ℝ) + normalizedStringValue b Y.1)) := by
    intro Y
    have hat : (b : ℝ) * normalizedStringValue b (a :: Y.1)
        = (a.val : ℝ) + normalizedStringValue b Y.1 :=
      atom_cons b hb _ _
    rw [weight_cons_toReal b hb _ _, hat]
    ring
  let σ : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k} ≃
      {Y : List (Fin b) // Y.count ⟨d, hd⟩ = k} :=
    Equiv.subtypeEquivProp (fiber_same_eq b d hd k a ha)
  calc (∑' Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
          (stringWeight b (a :: Y.1)).toReal
            * f ((b : ℝ) * normalizedStringValue b (a :: Y.1)))
      = ∑' Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
          (1 / (b : ℝ))
            * ((stringWeight b Y.1).toReal
              * f ((a.val : ℝ) + normalizedStringValue b Y.1)) :=
        tsum_congr hterm
    _ = (1 / (b : ℝ)) * ∑' Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
          ((stringWeight b Y.1).toReal
            * f ((a.val : ℝ) + normalizedStringValue b Y.1)) :=
        tsum_mul_left
    _ = (1 / (b : ℝ)) * ∑' Z : {Z : List (Fin b) // Z.count ⟨d, hd⟩ = k},
          ((stringWeight b Z.1).toReal
            * f ((a.val : ℝ) + normalizedStringValue b Z.1)) := by
        congr 1
        rw [← σ.tsum_eq (fun Z : {Z : List (Fin b) // Z.count ⟨d, hd⟩ = k} =>
          ((stringWeight b Z.1).toReal
            * f ((a.val : ℝ) + normalizedStringValue b Z.1)))]
        refine tsum_congr fun Y => rfl
    _ = (1 / (b : ℝ))
          * ∫ x in Set.Ico (0 : ℝ) 1, f ((a.val : ℝ) + x) ∂irwinMeasure b d k hd := by
        congr 1
        exact (integral_eq_tsum b d hb hd (fun x => f ((a.val : ℝ) + x)) C
          (fun x hx => hC ((a.val : ℝ) + x) (add_mem_Ico b a.val a.isLt x hx))
          k).symm

end integralIrwinMeasureSucc

set_option linter.unusedVariables false in
/-- **Digit decomposition of the Irwin measures, positive index.** Let $b > 1$ and $d < b$ be
natural numbers, and for each natural number $j$ let $\mu_j$ be the Irwin measure of base $b$ and
digit $d$ with index $j$. Let $f : \mathbb{R} \to \mathbb{R}$ be measurable and bounded on
$[0, b)$, and let $k \ge 1$. Then
$$\int_{[0,1)} f(bx)\, d\mu_k(x) =
\frac{1}{b} \sum_{a \ne d} \int_{[0,1)} f(a + x)\, d\mu_k(x) +
\frac{1}{b} \int_{[0,1)} f(d + x)\, d\mu_{k-1}(x),$$
where $a$ ranges over the digits $0, 1, \dots, b - 1$ other than $d$.

Measurability of $f$ is a hypothesis added to the paper's boundedness assumption.

Source: Jean-François
Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
Article A11, Lemma 1. -/
public theorem integral_irwinMeasure_succ
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (f : ℝ → ℝ)
    (hf_measurable : Measurable f)
    (hf_bounded : Bornology.IsBounded (f '' Set.Ico (0 : ℝ) b))
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ x in Set.Ico (0 : ℝ) 1, f (b * x) ∂irwinMeasure b d k hd) =
      (1 / (b : ℝ)) *
        (∑ a ∈ Finset.range b,
          if a = d then 0 else
            ∫ x in Set.Ico (0 : ℝ) 1, f (a + x) ∂irwinMeasure b d k hd) +
      (1 / (b : ℝ)) *
        ∫ x in Set.Ico (0 : ℝ) 1, f (d + x) ∂irwinMeasure b d (k - 1) hd := by
  obtain ⟨C, hC⟩ := hf_bounded.exists_norm_le
  have hCf : ∀ y ∈ Set.Ico (0 : ℝ) (b : ℝ), ‖f y‖ ≤ C :=
    fun y hy => hC _ ⟨y, hy, rfl⟩
  have hCb : ∀ x ∈ Set.Ico (0 : ℝ) 1, ‖f ((b : ℝ) * x)‖ ≤ C := by
    intro x hx
    exact hC _ ⟨(b : ℝ) * x, integralIrwinMeasureSucc.mul_mem_Ico b hb x hx, rfl⟩
  have hLHS : (∫ x in Set.Ico (0 : ℝ) 1, f ((b : ℝ) * x) ∂irwinMeasure b d k hd)
      = ∑' X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k},
        (stringWeight b X.1).toReal * f ((b : ℝ) * normalizedStringValue b X.1) :=
    integralIrwinMeasureSucc.integral_eq_tsum b d hb hd (fun x => f ((b : ℝ) * x)) C
      hCb k
  have hF_summ : Summable (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
      (stringWeight b X.1).toReal * f ((b : ℝ) * normalizedStringValue b X.1)) :=
    integralIrwinMeasureSucc.summable_weight_mul b d hb hd (fun x => f ((b : ℝ) * x)) C
      hCb k
  set e := integralIrwinMeasureSucc.consEquiv b d k hd hk with he
  have hdecomp : (∑' X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k},
        (stringWeight b X.1).toReal * f ((b : ℝ) * normalizedStringValue b X.1))
      = ∑' a : Fin b, ∑' Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
        (stringWeight b (a :: Y.1)).toReal
          * f ((b : ℝ) * normalizedStringValue b (a :: Y.1)) := by
    have h1 : (∑' X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k},
          (stringWeight b X.1).toReal * f ((b : ℝ) * normalizedStringValue b X.1))
        = ∑' p : Σ a : Fin b, {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
          (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
            (stringWeight b X.1).toReal * f ((b : ℝ) * normalizedStringValue b X.1))
            (e.symm p) :=
      (e.symm.tsum_eq _).symm
    have hFsumm : Summable (fun p : Σ a : Fin b,
          {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k} =>
        (stringWeight b (p.1 :: p.2.1)).toReal
          * f ((b : ℝ) * normalizedStringValue b (p.1 :: p.2.1))) :=
      (e.symm.summable_iff).mpr hF_summ
    have hfib : ∀ a : Fin b,
        Summable (fun Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k} =>
          (stringWeight b (a :: Y.1)).toReal
            * f ((b : ℝ) * normalizedStringValue b (a :: Y.1))) := by
      intro a
      by_cases ha : a = ⟨d, hd⟩
      · exact integralIrwinMeasureSucc.fiber_summable_of_eq b d hb hd f C hCf k hk
          a ha
      · exact integralIrwinMeasureSucc.fiber_summable_of_ne b d hb hd f C hCf k
          a ha
    have h2 : (∑' p : Σ a : Fin b, {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
          (stringWeight b (p.1 :: p.2.1)).toReal
            * f ((b : ℝ) * normalizedStringValue b (p.1 :: p.2.1)))
        = ∑' a : Fin b, ∑' Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
          (stringWeight b (a :: Y.1)).toReal
            * f ((b : ℝ) * normalizedStringValue b (a :: Y.1)) :=
      Summable.tsum_sigma' hfib hFsumm
    rw [h1]
    have hbridge : (∑' p : Σ a : Fin b, {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
          (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
            (stringWeight b X.1).toReal * f ((b : ℝ) * normalizedStringValue b X.1))
            (e.symm p))
        = ∑' p : Σ a : Fin b, {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
          (stringWeight b (p.1 :: p.2.1)).toReal
            * f ((b : ℝ) * normalizedStringValue b (p.1 :: p.2.1)) :=
      tsum_congr fun p => rfl
    rw [hbridge, h2]
  rw [hLHS, hdecomp, tsum_fintype]
  have hVd : (∑' Y : {Y : List (Fin b) // (⟨d, hd⟩ :: Y).count ⟨d, hd⟩ = k},
        (stringWeight b (⟨d, hd⟩ :: Y.1)).toReal
          * f ((b : ℝ) * normalizedStringValue b (⟨d, hd⟩ :: Y.1)))
      = (1 / (b : ℝ))
        * ∫ x in Set.Ico (0 : ℝ) 1, f ((d : ℝ) + x) ∂irwinMeasure b d (k - 1) hd :=
    integralIrwinMeasureSucc.fiber_tsum_of_eq b d hb hd f C hCf k hk _ rfl
  have hVa : ∀ a : Fin b, a ≠ ⟨d, hd⟩ →
      (∑' Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
        (stringWeight b (a :: Y.1)).toReal
          * f ((b : ℝ) * normalizedStringValue b (a :: Y.1)))
      = (1 / (b : ℝ))
        * ∫ x in Set.Ico (0 : ℝ) 1, f ((a.val : ℝ) + x) ∂irwinMeasure b d k hd :=
    fun a ha => integralIrwinMeasureSucc.fiber_tsum_of_ne b d hb hd f C hCf k a ha
  have hsplit : (∑ a : Fin b, ∑' Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
        (stringWeight b (a :: Y.1)).toReal
          * f ((b : ℝ) * normalizedStringValue b (a :: Y.1)))
      = (∑ a ∈ Finset.univ.erase (⟨d, hd⟩ : Fin b),
          ∑' Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
          (stringWeight b (a :: Y.1)).toReal
            * f ((b : ℝ) * normalizedStringValue b (a :: Y.1)))
        + (∑' Y : {Y : List (Fin b) // (⟨d, hd⟩ :: Y).count ⟨d, hd⟩ = k},
          (stringWeight b (⟨d, hd⟩ :: Y.1)).toReal
            * f ((b : ℝ) * normalizedStringValue b (⟨d, hd⟩ :: Y.1))) :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm
  rw [hsplit, hVd]
  have herase : (∑ a ∈ Finset.univ.erase (⟨d, hd⟩ : Fin b),
          ∑' Y : {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = k},
          (stringWeight b (a :: Y.1)).toReal
            * f ((b : ℝ) * normalizedStringValue b (a :: Y.1)))
        = ∑ a ∈ Finset.univ.erase (⟨d, hd⟩ : Fin b),
          (1 / (b : ℝ))
            * ∫ x in Set.Ico (0 : ℝ) 1, f ((a.val : ℝ) + x) ∂irwinMeasure b d k hd := by
    refine Finset.sum_congr rfl fun a ha => hVa a ?_
    exact (Finset.mem_erase.mp ha).1
  rw [herase, Finset.mul_sum]
  have hrange : (∑ a ∈ Finset.range b,
          (1 / (b : ℝ)) * (if a = d then (0 : ℝ) else
            ∫ x in Set.Ico (0 : ℝ) 1, f ((a : ℝ) + x) ∂irwinMeasure b d k hd))
        = ∑ a : Fin b, (1 / (b : ℝ)) * (if a.val = d then (0 : ℝ) else
          ∫ x in Set.Ico (0 : ℝ) 1, f ((a.val : ℝ) + x) ∂irwinMeasure b d k hd) :=
    (Fin.sum_univ_eq_sum_range _ b).symm
  rw [hrange]
  have hsplit2 : (∑ a : Fin b, (1 / (b : ℝ)) * (if a.val = d then (0 : ℝ) else
          ∫ x in Set.Ico (0 : ℝ) 1, f ((a.val : ℝ) + x) ∂irwinMeasure b d k hd))
        = (∑ a ∈ Finset.univ.erase (⟨d, hd⟩ : Fin b), (1 / (b : ℝ)) * (if a.val = d then
            (0 : ℝ) else
            ∫ x in Set.Ico (0 : ℝ) 1, f ((a.val : ℝ) + x) ∂irwinMeasure b d k hd))
          + (1 / (b : ℝ)) * (if (⟨d, hd⟩ : Fin b).val = d then (0 : ℝ) else
            ∫ x in Set.Ico (0 : ℝ) 1,
              f (((⟨d, hd⟩ : Fin b).val : ℝ) + x) ∂irwinMeasure b d k hd) :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm
  rw [hsplit2]
  have hd0 : (1 / (b : ℝ)) * (if (⟨d, hd⟩ : Fin b).val = d then (0 : ℝ) else
      ∫ x in Set.Ico (0 : ℝ) 1,
        f (((⟨d, hd⟩ : Fin b).val : ℝ) + x) ∂irwinMeasure b d k hd) = 0 := by
    rw [ite_eq_left rfl]
    ring
  rw [hd0, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  have hne : a.val ≠ d := fun h => (Finset.mem_erase.mp ha).1 (Fin.ext h)
  rw [ite_eq_right hne]

end

end MetaMathlibExt
