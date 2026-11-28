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
# Digit decomposition of the Irwin measures

For a natural base `b > 1`, a digit `d < b`, and a measurable real function `f` bounded on
`[0, b)`, the integral of `f (b * x)` over `[0, 1)` against `μₖ` splits by leading digit.
For `k ≥ 1` the digit `d` gives a predecessor-index integral and the other digits give
same-index integrals, each weighted by `1 / b`. For `k = 0` only digits other than `d`
can lead a nonempty string, and the empty string contributes `f 0`.

## References

* Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
  Article A11, pp. 1–20, Lemma 1 (zero-index identity: equation (3), p. 11).
* Jean-François Burnol, *Moments in the Exact Summation of the Curious Series of Kempner Type*,
  The American Mathematical Monthly 132 (10) (2025), pp. 995–1006, Lemma 7.
  As noted in Remark 7 of the Irwin paper, this earlier result excludes the binary case
  `b = 2`, `d = 1` (where the only allowed digit is `0`).
* The zero-index Lean proof adapts the reindexing in `integral_irwinMeasure_succ` in this module
  and uses the same `integral_eq_tsum`, `summable_weight_mul` and `fiber_tsum_of_ne`.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators ENNReal
open Filter MeasureTheory Set

namespace integralIrwinMeasureSucc

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
        mul_le_mul_of_nonneg_left (hC _ (normalizedStringValue_mem_Ico b hb X.1))
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
    fun X => normalizedStringValue_mem_Ico b hb X.1
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

set_option linter.unusedVariables false in
/-- **Digit decomposition of the Irwin measure, zero index.** Let $b > 1$ and $d < b$ be natural
numbers, and let $\mu_0$ be the Irwin measure of base $b$ and digit $d$ with index $0$. For every
measurable function $f : \mathbb{R} \to \mathbb{R}$ that is bounded on $[0, b)$,
$$\int_{[0,1)} f(bx)\, d\mu_0(x) = f(0) +
\frac{1}{b} \sum_{a \ne d} \int_{[0,1)} f(a + x)\, d\mu_0(x),$$
where $a$ ranges over the digits $0, 1, \dots, b - 1$ other than $d$.

Measurability of $f$ is a hypothesis added to the paper's boundedness assumption.

Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, Lemma 1. -/
public theorem integral_irwinMeasure_zero
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (f : ℝ → ℝ)
    (hf_measurable : Measurable f)
    (hf_bounded : Bornology.IsBounded (f '' Set.Ico (0 : ℝ) b)) :
    (∫ x in Set.Ico (0 : ℝ) 1, f (b * x) ∂irwinMeasure b d 0 hd) =
      f 0 + (1 / (b : ℝ)) *
        ∑ a ∈ Finset.range b,
          if a = d then 0 else
            ∫ x in Set.Ico (0 : ℝ) 1, f (a + x) ∂irwinMeasure b d 0 hd := by
  obtain ⟨C, hC⟩ := hf_bounded.exists_norm_le
  have hCf : ∀ y ∈ Set.Ico (0 : ℝ) (b : ℝ), ‖f y‖ ≤ C :=
    fun y hy => hC _ ⟨y, hy, rfl⟩
  have hCb : ∀ x ∈ Set.Ico (0 : ℝ) 1, ‖f ((b : ℝ) * x)‖ ≤ C :=
    fun x hx => hCf _ (integralIrwinMeasureSucc.mul_mem_Ico b hb x hx)
  let F (X : {X : List (Fin b) // X.count ⟨d, hd⟩ = 0}) :=
    (stringWeight b X.1).toReal * f ((b : ℝ) * normalizedStringValue b X.1)
  have hF : Summable F :=
    integralIrwinMeasureSucc.summable_weight_mul b d hb hd _ C hCb 0
  -- Keep the empty string separate from the fibers indexed by a leading digit.
  let S (a : Fin b) := {Y : List (Fin b) // (a :: Y).count ⟨d, hd⟩ = 0}
  let e : Unit ⊕ (Σ a : Fin b, S a) ≃ {X : List (Fin b) // X.count ⟨d, hd⟩ = 0} :=
    { toFun := fun
        | .inl _ => ⟨[], rfl⟩
        | .inr ⟨a, Y⟩ => ⟨a :: Y.1, Y.2⟩
      invFun := fun
        | ⟨[], _⟩ => .inl ()
        | ⟨a :: Y, hY⟩ => .inr ⟨a, ⟨Y, hY⟩⟩
      left_inv := by rintro (⟨⟩ | ⟨a, Y⟩) <;> rfl
      right_inv := by rintro ⟨X, hX⟩; cases X <;> rfl }
  have hReindexed : Summable (F ∘ e) := e.summable_iff.mpr hF
  have hTail : Summable (fun p : Σ a : Fin b, S a => F (e (.inr p))) :=
    hReindexed.comp_injective Sum.inr_injective
  have hEmpty : (∑' u : Unit, F (e (.inl u))) = f 0 := by
    simp [tsum_fintype, F, e, stringWeight, normalizedStringValue, stringValue]
  rw [integralIrwinMeasureSucc.integral_eq_tsum b d hb hd _ C hCb 0]
  change (∑' X, F X) = _
  rw [← e.tsum_eq F,
    Summable.tsum_sum (f := fun c => F (e c))
      (hReindexed.comp_injective Sum.inl_injective) hTail,
    hEmpty, hTail.tsum_sigma, tsum_fintype, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  change (∑' Y : S a, (stringWeight b (a :: Y.1)).toReal *
      f ((b : ℝ) * normalizedStringValue b (a :: Y.1))) = _
  by_cases ha : a.val = d
  · have hae : a = (⟨d, hd⟩ : Fin b) := Fin.ext ha
    subst a
    have : IsEmpty (S ⟨d, hd⟩) := ⟨fun Y => by simpa using Y.2⟩
    simp
  · rw [ite_eq_right ha]
    exact integralIrwinMeasureSucc.fiber_tsum_of_ne b d hb hd f C hCf 0 a
      (fun h => ha (congrArg Fin.val h))

end

end MetaMathlibExt
