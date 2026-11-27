/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Round
public import Mathlib.Order.Interval.Set.Defs
public import MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# DAC level error

## i. Overview

A digital-to-analog converter (DAC) with step `Δ` and integer codes
`k` in a finite range `Set.Icc kmin kmax` ideally outputs the level
`Δ * k`. The actual level of code `k` is modelled here as
`dacLevel Δ e k = Δ * k + e k`, where `e k` is the level error at
code `k`, bounded by `|e k| ≤ η` on the code range only. The ideal
code-to-voltage map `Δ * k` is the same map used by the saturating
round-half-up analog-to-digital converter in
`MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp`, whose integer
code `code` and clipping predicate `IsClipped` are reused directly,
so an unclipped analog-to-digital code can be composed with this
DAC. Adjacent codes are adjacent decoded integer values `k` and
`k + 1`; for signed codes, decoded by `BitVec.toInt`, the successor
of the maximal signed code wraps to the minimal signed code and is
not an adjacent step.

## ii. Key results

- `abs_dacLevel_add_one_sub_sub_le`: the adjacent step error, the
  deviation of an adjacent level step from the ideal step `Δ`, is
  at most `2 * η` (the differential nonlinearity bound).
- `dacLevel_strictMonoOn`: if `2 * η < Δ`, the levels are strictly
  increasing on the code range.
- `abs_dacLevel_code_sub_le_of_not_isClipped`: composing an
  unclipped saturating round-half-up code with this DAC gives an
  output within `Δ / 2 + η` of the input.
- `dacLevel_correct`: the three clauses together.
- `exists_not_strictMonoOn_of_le_two_mul`: the monotonicity
  threshold is sharp; once `Δ ≤ 2 * η`, some admissible level error
  makes the levels nonmonotone.

## iii. Table of contents

- A. DAC levels
- B. ADC-to-DAC composition
- C. Validation

## iv. References

- B. Razavi, *Design of Analog CMOS Integrated Circuits*, 2nd ed.,
  McGraw-Hill Education, 2017: data-converter transfer
  characteristics, quantization error, and differential
  nonlinearity of digital-to-analog converters.
- D. Johns and K. Martin, *Analog Integrated Circuit Design*, 2nd
  ed., Wiley, 2012: Nyquist-rate digital-to-analog converters and
  their static transfer error.

## A. DAC levels

The level error is bounded only on the code range, where the DAC
has levels; errors outside the range are unconstrained.

## B. ADC-to-DAC composition

The composition reuses the saturating code `code` and the clipping
predicate `IsClipped` of
`MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp`. Away from
clipping, the code is the plain rounded code, and the composed
error splits into the round-half-up quantization error `Δ / 2` and
the DAC level error `η`.

## C. Validation

A statement that BitVec wraparound from the maximal to the minimal
signed code is not a monotone adjacent step, and the sharpness
witness for the monotonicity threshold.
-/

@[expose] public section

namespace PhyslibExt.Instrumentation.DACLevelError

open MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp Set

/-- The unclipped event, restated as the rounded code lying in the
code range. The saturating round-half-up module provides the code
equation `code_eq_round_of_not_isClipped` but no such
characterization of the clipping predicate, so it is kept here. -/
private lemma not_isClipped_iff {Δ : ℝ} {kmin kmax : ℤ} {x : ℝ} :
    ¬ IsClipped Δ kmin kmax x ↔ kmin ≤ round (x / Δ) ∧ round (x / Δ) ≤ kmax := by
  simp only [IsClipped, not_or, not_lt]

/-- The actual output level of a DAC for integer code `k`: the
code-to-voltage value `Δ * k` plus the level error `e k`. -/
def dacLevel (Δ : ℝ) (e : ℤ → ℝ) (k : ℤ) : ℝ :=
  Δ * (k : ℝ) + e k

/-- The level error is the deviation of the actual level from the
ideal level `Δ * k`. -/
lemma dacLevel_sub_mul (Δ : ℝ) (e : ℤ → ℝ) (k : ℤ) :
    dacLevel Δ e k - Δ * (k : ℝ) = e k := by
  unfold dacLevel
  ring

/-- **Adjacent step error.** If `|e k| ≤ η` on the code range and
`k`, `k + 1` are both codes, the step between adjacent levels
differs from the ideal step `Δ` by at most `2 * η`. -/
theorem abs_dacLevel_add_one_sub_sub_le {Δ η : ℝ} {kmin kmax : ℤ} {e : ℤ → ℝ}
    (he : ∀ k ∈ Icc kmin kmax, |e k| ≤ η) {k : ℤ} (hk : kmin ≤ k) (hk1 : k + 1 ≤ kmax) :
    |dacLevel Δ e (k + 1) - dacLevel Δ e k - Δ| ≤ 2 * η := by
  have hkmax : k ≤ kmax := by omega
  have hkmin1 : kmin ≤ k + 1 := by omega
  have h1 := he k (mem_Icc.mpr ⟨hk, hkmax⟩)
  have h2 := he (k + 1) (mem_Icc.mpr ⟨hkmin1, hk1⟩)
  have hstep : dacLevel Δ e (k + 1) - dacLevel Δ e k - Δ = e (k + 1) - e k := by
    unfold dacLevel
    push_cast
    ring
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp h1
  obtain ⟨h2lo, h2hi⟩ := abs_le.mp h2
  rw [hstep, abs_le]
  constructor <;> linarith

/-- **Strict monotonicity.** If `|e k| ≤ η` on the code range and
`2 * η < Δ`, the DAC levels are strictly increasing on the code
range. -/
theorem dacLevel_strictMonoOn {Δ η : ℝ} {kmin kmax : ℤ} {e : ℤ → ℝ}
    (he : ∀ k ∈ Icc kmin kmax, |e k| ≤ η) (hη : 2 * η < Δ) :
    StrictMonoOn (dacLevel Δ e) (Icc kmin kmax) := by
  intro a ha b hb hab
  obtain ⟨hea1, hea2⟩ := abs_le.mp (he a ha)
  obtain ⟨heb1, heb2⟩ := abs_le.mp (he b hb)
  have hη0 : 0 ≤ η := (abs_nonneg (e a)).trans (he a ha)
  have hΔ : 0 < Δ := by linarith
  have hab1 : (a : ℝ) + 1 ≤ (b : ℝ) := by
    have h : a + 1 ≤ b := by omega
    exact_mod_cast h
  have hmul : Δ * 1 ≤ Δ * ((b : ℝ) - (a : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hΔ.le
  simp only [dacLevel]
  linarith

/-- **Unclipped ADC code through the DAC.** For `Δ > 0`, `|e k| ≤ η`
on the code range and an input `x` that the ADC does not clip, the
DAC output at the ADC code of `x` is within `Δ / 2 + η` of `x`. -/
theorem abs_dacLevel_code_sub_le_of_not_isClipped {Δ η : ℝ} (hΔ : 0 < Δ) {kmin kmax : ℤ}
    {e : ℤ → ℝ} (he : ∀ k ∈ Icc kmin kmax, |e k| ≤ η) {x : ℝ}
    (hx : ¬ IsClipped Δ kmin kmax x) :
    |dacLevel Δ e (code Δ kmin kmax x) - x| ≤ Δ / 2 + η := by
  have hΔne : Δ ≠ 0 := ne_of_gt hΔ
  obtain ⟨hlo, hhi⟩ := not_isClipped_iff.mp hx
  have hcode : code Δ kmin kmax x = round (x / Δ) := code_eq_round_of_not_isClipped hx
  have hmem : code Δ kmin kmax x ∈ Icc kmin kmax := by
    rw [hcode]
    exact mem_Icc.mpr ⟨hlo, hhi⟩
  have hec := he _ hmem
  have hscale : |x - Δ * ((round (x / Δ) : ℤ) : ℝ)| ≤ Δ / 2 := by
    have hpt : x - Δ * ((round (x / Δ) : ℤ) : ℝ)
        = Δ * (x / Δ - ((round (x / Δ) : ℤ) : ℝ)) := by
      field_simp
    rw [hpt, abs_mul, abs_of_pos hΔ]
    calc Δ * |x / Δ - ((round (x / Δ) : ℤ) : ℝ)|
        ≤ Δ * (1 / 2) := mul_le_mul_of_nonneg_left (abs_sub_round (x / Δ)) hΔ.le
      _ = Δ / 2 := by ring
  have hdecomp : dacLevel Δ e (round (x / Δ)) - x
      = (Δ * ((round (x / Δ) : ℤ) : ℝ) - x) + e (round (x / Δ)) := by
    unfold dacLevel
    ring
  have hscale' : |Δ * ((round (x / Δ) : ℤ) : ℝ) - x| ≤ Δ / 2 := by
    rw [abs_sub_comm]
    exact hscale
  obtain ⟨hs1, hs2⟩ := abs_le.mp hscale'
  rw [hcode] at hec ⊢
  obtain ⟨he1, he2⟩ := abs_le.mp hec
  rw [hdecomp, abs_le]
  constructor <;> linarith

/-- **Full-scale form.** For inputs in the full-scale interval
`[Δ * kmin, Δ * kmax]` the composed error is at most `Δ / 2 + η`. -/
lemma abs_dacLevel_code_sub_le_of_mem_Icc {Δ η : ℝ} (hΔ : 0 < Δ) {kmin kmax : ℤ}
    {e : ℤ → ℝ} (he : ∀ k ∈ Icc kmin kmax, |e k| ≤ η) {x : ℝ}
    (hx : x ∈ Icc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))) :
    |dacLevel Δ e (code Δ kmin kmax x) - x| ≤ Δ / 2 + η := by
  exact abs_dacLevel_code_sub_le_of_not_isClipped hΔ he (not_isClipped_of_mem_Icc hΔ hx)

/-- **Signed `w`-bit form.** For `1 ≤ w`, the signed code range
`[signedMinCode w, signedMaxCode w]` of the ADC, `Δ > 0`,
`|e k| ≤ η` on that range and an unclipped input `x`, the composed
error is at most `Δ / 2 + η`. -/
lemma abs_dacLevel_code_signed_sub_le_of_not_isClipped {Δ η : ℝ} (hΔ : 0 < Δ) {w : ℕ}
    (hw : 1 ≤ w) {e : ℤ → ℝ}
    (he : ∀ k ∈ Icc (signedMinCode w) (signedMaxCode w), |e k| ≤ η)
    {x : ℝ} (hx : ¬ IsClipped Δ (signedMinCode w) (signedMaxCode w) x) :
    |dacLevel Δ e (code Δ (signedMinCode w) (signedMaxCode w) x) - x| ≤ Δ / 2 + η := by
  exact abs_dacLevel_code_sub_le_of_not_isClipped hΔ he hx

/-- **DAC level contract.** For `Δ > 0` and `|e k| ≤ η` on the code
range: adjacent steps are within `2 * η` of `Δ`; the levels are
strictly increasing when `2 * η < Δ`; and the DAC output at the
code of any unclipped input `x` is within `Δ / 2 + η` of `x`. -/
theorem dacLevel_correct {Δ η : ℝ} (hΔ : 0 < Δ) {kmin kmax : ℤ} {e : ℤ → ℝ}
    (he : ∀ k ∈ Icc kmin kmax, |e k| ≤ η) :
    (∀ k : ℤ, kmin ≤ k → k + 1 ≤ kmax → |dacLevel Δ e (k + 1) - dacLevel Δ e k - Δ| ≤ 2 * η) ∧
      (2 * η < Δ → StrictMonoOn (dacLevel Δ e) (Icc kmin kmax)) ∧
      (∀ x : ℝ, ¬ IsClipped Δ kmin kmax x →
        |dacLevel Δ e (code Δ kmin kmax x) - x| ≤ Δ / 2 + η) := by
  exact ⟨fun k hk hk1 => abs_dacLevel_add_one_sub_sub_le he hk hk1,
    fun h => dacLevel_strictMonoOn he h,
    fun x hx => abs_dacLevel_code_sub_le_of_not_isClipped hΔ he hx⟩

/-- **BitVec wraparound is not an adjacent monotone step.** For
`1 ≤ w`, `|e k| ≤ η` on the signed `w`-bit range and `2 * η < Δ`:
the BitVec successor of the maximal signed code decodes to a value
that is not the next integer code, and its DAC level is strictly
below that of the maximal code. -/
lemma dacLevel_toInt_intMax_add_one_lt {Δ η : ℝ} {w : ℕ} (hw : 1 ≤ w) {e : ℤ → ℝ}
    (he : ∀ k ∈ Icc (signedMinCode w) (signedMaxCode w), |e k| ≤ η) (hη : 2 * η < Δ) :
    (BitVec.intMax w + 1).toInt ≠ (BitVec.intMax w).toInt + 1 ∧
      dacLevel Δ e (BitVec.intMax w + 1).toInt < dacLevel Δ e (BitVec.intMax w).toInt := by
  have hne : NeZero w := ⟨by omega⟩
  have hadd : BitVec.intMax w + 1 = BitVec.intMin w := BitVec.intMax_add_one
  have hmin : (BitVec.intMax w + 1).toInt = (-2 ^ (w - 1) : ℤ) := by
    rw [hadd, BitVec.toInt_intMin]
    have hmod : (2 : ℕ) ^ (w - 1) % 2 ^ w = 2 ^ (w - 1) :=
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
    rw [hmod]
    push_cast
    ring
  have hmax : (BitVec.intMax w).toInt = (2 ^ (w - 1) - 1 : ℤ) := BitVec.toInt_intMax
  have hpow : (1 : ℤ) ≤ 2 ^ (w - 1) := one_le_pow₀ (by norm_num)
  have hminS : (BitVec.intMax w + 1).toInt = signedMinCode w := by
    unfold signedMinCode
    exact hmin
  have hmaxS : (BitVec.intMax w).toInt = signedMaxCode w := by
    unfold signedMaxCode
    exact hmax
  rw [hminS, hmaxS]
  have hmono := dacLevel_strictMonoOn he hη
  have hmem1 : signedMinCode w ∈ Icc (signedMinCode w) (signedMaxCode w) :=
    mem_Icc.mpr ⟨le_refl _, signedMinCode_le_signedMaxCode hw⟩
  have hmem2 : signedMaxCode w ∈ Icc (signedMinCode w) (signedMaxCode w) :=
    mem_Icc.mpr ⟨signedMinCode_le_signedMaxCode hw, le_refl _⟩
  have hlt : signedMinCode w < signedMaxCode w := by
    unfold signedMinCode signedMaxCode
    linarith [hpow]
  constructor
  · intro hcon
    linarith
  · exact hmono hmem1 hmem2 hlt

/-- **`η ≥ Δ / 2` can permit a nonmonotone DAC.** For every `Δ > 0`
and `η` with `Δ ≤ 2 * η`, some level error bounded by `η` on the
codes `{0, 1}` makes the DAC levels not strictly increasing. -/
theorem exists_not_strictMonoOn_of_le_two_mul {Δ η : ℝ} (hΔ : 0 < Δ) (hη : Δ ≤ 2 * η) :
    ∃ e : ℤ → ℝ, (∀ k ∈ Icc (0 : ℤ) 1, |e k| ≤ η) ∧
      ¬ StrictMonoOn (dacLevel Δ e) (Icc (0 : ℤ) 1) := by
  refine ⟨fun k => if k = 0 then Δ / 2 else -(Δ / 2), ?_, ?_⟩
  · intro k hk
    rw [mem_Icc] at hk
    have hk01 : k = 0 ∨ k = 1 := by omega
    have hnn : (0 : ℝ) ≤ Δ / 2 := by linarith
    have hle : Δ / 2 ≤ η := by linarith
    show |if k = 0 then Δ / 2 else -(Δ / 2)| ≤ η
    rcases hk01 with rfl | rfl
    · have hif0 : (if (0 : ℤ) = 0 then Δ / 2 else -(Δ / 2)) = Δ / 2 := ite_eq_left rfl
      rw [hif0, abs_of_nonneg hnn]
      exact hle
    · have hif1 : (if (1 : ℤ) = 0 then Δ / 2 else -(Δ / 2)) = -(Δ / 2) :=
        ite_eq_right (by norm_num)
      rw [hif1, abs_neg, abs_of_nonneg hnn]
      exact hle
  · intro hmono
    have hif0 : (if (0 : ℤ) = 0 then Δ / 2 else -(Δ / 2)) = Δ / 2 := ite_eq_left rfl
    have hif1 : (if (1 : ℤ) = 0 then Δ / 2 else -(Δ / 2)) = -(Δ / 2) := ite_eq_right (by norm_num)
    have h0 : (0 : ℤ) ∈ Icc (0 : ℤ) 1 := mem_Icc.mpr ⟨le_refl _, by norm_num⟩
    have h1m : (1 : ℤ) ∈ Icc (0 : ℤ) 1 := mem_Icc.mpr ⟨by norm_num, le_refl _⟩
    have h01 := hmono h0 h1m (by norm_num : (0 : ℤ) < 1)
    have heq : dacLevel Δ (fun k => if k = 0 then Δ / 2 else -(Δ / 2)) 0
        = dacLevel Δ (fun k => if k = 0 then Δ / 2 else -(Δ / 2)) 1 := by
      show Δ * ((0 : ℤ) : ℝ) + (if (0 : ℤ) = 0 then Δ / 2 else -(Δ / 2))
        = Δ * ((1 : ℤ) : ℝ) + (if (1 : ℤ) = 0 then Δ / 2 else -(Δ / 2))
      rw [hif0, hif1]
      push_cast
      ring
    rw [heq] at h01
    exact lt_irrefl _ h01

end PhyslibExt.Instrumentation.DACLevelError
