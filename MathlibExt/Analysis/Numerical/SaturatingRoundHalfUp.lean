/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Round
public import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Saturating round-half-up quantization

For a step `Delta > 0` and integer code endpoints `kmin <= kmax`, the
saturating analog-to-digital quantizer is
`Q(x) = Delta * clamp(kmin, kmax, floor(x / Delta + 1 / 2))`, where
rounding is to nearest with ties toward `+infinity`. This module proves
the explicit quantization contract: `Q` is monotone, the error is at
most `Delta / 2` on every unclipped input, in particular on the
full-scale interval `[Delta * kmin, Delta * kmax]`,
and for arbitrary inputs the error is at most the distance to that
interval plus `Delta / 2`. Clipping is exposed separately as
`IsClipped`, and signed `w`-bit codes (`w >= 1`) are handled with the
code-to-voltage map `Delta * (code : Real)`.

Encoding notes:

* Mathlib `round y = floor(y + 1 / 2)` (`round_eq`), so `round (x / Delta)`
  is exactly the `floor(x / Delta + 1 / 2)` above; see
  `code_eq_floor_add_half`.
* `clamp(kmin, kmax, r)` is `max kmin (min kmax r)` on the integers.
* The distance to the full-scale interval is represented by the Mathlib
  interval projection `Set.projIcc`: its coercion to `Real` is the
  nearest point of the interval, and `abs_sub_projIcc_le` identifies
  `|x - (Set.projIcc ... x : Real)|` as that distance. The endpoint
  ordering needed by `Set.projIcc` is the named lemma `fullScale_le`.
* Signed `w`-bit codes are `-(2 ^ (w - 1)) .. 2 ^ (w - 1) - 1`, only
  under `1 <= w`.

The unclipped `Delta / 2` bound is not guaranteed for clipped inputs:
some violate it (`Delta = 1`, singleton code range, `x = 10` has error
`10`), while others still meet it (`x = 1 / 2` in the same range is
clipped and has error exactly `Delta / 2`). No probabilistic model of
the quantization error is asserted.
-/

@[expose] public section

namespace MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp

/-- Monotonicity of `round` on `ℝ`, via `round_eq` and `Int.floor_mono`. -/
private theorem round_mono_real : Monotone (round : ℝ → ℤ) := by
  intro a b hab
  rw [round_eq, round_eq]
  apply Int.floor_mono
  linarith

/-- Triangle inequality for `|· - ·|`. -/
private theorem abs_sub_le_mid (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
  have h : a - c = (a - b) + (b - c) := by ring
  rw [h]
  exact abs_add_le _ _

/-- Cancellation of a nonzero scaling. -/
private theorem mul_div_cancel_real (Δ : ℝ) (hΔ : 0 < Δ) (k : ℝ) :
    (Δ * k) / Δ = k := by
  have hΔ0 : Δ ≠ 0 := ne_of_gt hΔ
  rw [div_eq_iff hΔ0]
  ring

/-- The saturating integer code of `x` for step `Δ` and code range
`[kmin, kmax]`: round `x / Δ` to the nearest integer (ties toward `+∞`),
then clamp into the code range. -/
noncomputable def code (Δ : ℝ) (kmin kmax : ℤ) (x : ℝ) : ℤ :=
  max kmin (min kmax (round (x / Δ)))

/-- The reconstructed (quantized) value `Δ * code`: the code-to-voltage map
applied to the saturating code. -/
noncomputable def quantize (Δ : ℝ) (kmin kmax : ℤ) (x : ℝ) : ℝ :=
  Δ * (code Δ kmin kmax x : ℝ)

/-- The input `x` is clipped when its unclamped rounded code lies outside
the code range `[kmin, kmax]`. -/
def IsClipped (Δ : ℝ) (kmin kmax : ℤ) (x : ℝ) : Prop :=
  round (x / Δ) < kmin ∨ kmax < round (x / Δ)

/-- The least signed `w`-bit code, `-(2 ^ (w - 1))`. Meaningful for
`1 <= w`; the theorems below carry that hypothesis. -/
def signedMinCode (w : ℕ) : ℤ := -(2 : ℤ) ^ (w - 1)

/-- The greatest signed `w`-bit code, `2 ^ (w - 1) - 1`. Meaningful for
`1 <= w`; the theorems below carry that hypothesis. -/
def signedMaxCode (w : ℕ) : ℤ := (2 : ℤ) ^ (w - 1) - 1

/-- The endpoints of the full-scale interval are ordered, as required
by the Mathlib interval projection `Set.projIcc`. -/
theorem fullScale_le {Δ : ℝ} (hΔ : 0 < Δ) {kmin kmax : ℤ} (hk : kmin ≤ kmax) :
    Δ * (kmin : ℝ) ≤ Δ * (kmax : ℝ) := by
  exact mul_le_mul_of_nonneg_left (Int.cast_le.mpr hk) hΔ.le

/-- The code in floor form: `round y = ⌊y + 1 / 2⌋`. -/
theorem code_eq_floor_add_half (Δ : ℝ) (kmin kmax : ℤ) (x : ℝ) :
    code Δ kmin kmax x = max kmin (min kmax ⌊x / Δ + 1 / 2⌋) := by
  unfold code
  rw [round_eq]

/-- The saturating code always lies in the code range. -/
theorem code_mem_Icc {kmin kmax : ℤ} (hk : kmin ≤ kmax) (Δ : ℝ) (x : ℝ) :
    code Δ kmin kmax x ∈ Set.Icc kmin kmax := by
  unfold code
  rw [Set.mem_Icc]
  exact ⟨le_max_left _ _, max_le hk (min_le_left _ _)⟩

/-- Away from clipping, the saturating code is the plain rounded code. -/
theorem code_eq_round_of_not_isClipped {Δ : ℝ} {kmin kmax : ℤ} {x : ℝ}
    (h : ¬ IsClipped Δ kmin kmax x) :
    code Δ kmin kmax x = round (x / Δ) := by
  unfold IsClipped at h
  have hlo : kmin ≤ round (x / Δ) := le_of_not_gt (fun hh => h (Or.inl hh))
  have hhi : round (x / Δ) ≤ kmax := le_of_not_gt (fun hh => h (Or.inr hh))
  unfold code
  rw [min_eq_right hhi, max_eq_right hlo]

/-- Below-range inputs saturate to the least code. -/
theorem code_eq_kmin_of_round_lt {Δ : ℝ} {kmin kmax : ℤ} {x : ℝ}
    (h : round (x / Δ) < kmin) :
    code Δ kmin kmax x = kmin := by
  unfold code
  rw [max_eq_left (le_of_lt (lt_of_le_of_lt (min_le_right _ _) h))]

/-- Above-range inputs saturate to the greatest code. -/
theorem code_eq_kmax_of_kmax_lt_round {Δ : ℝ} {kmin kmax : ℤ} {x : ℝ}
    (hk : kmin ≤ kmax) (h : kmax < round (x / Δ)) :
    code Δ kmin kmax x = kmax := by
  unfold code
  rw [min_eq_left (le_of_lt h), max_eq_right hk]

/-- The saturating code is monotone in the input. -/
theorem code_mono {Δ : ℝ} (hΔ : 0 < Δ) (kmin kmax : ℤ) :
    Monotone (code Δ kmin kmax) := by
  intro a b hab
  have hdiv : a / Δ ≤ b / Δ := (div_le_div_iff_of_pos_right hΔ).mpr hab
  have hr : round (a / Δ) ≤ round (b / Δ) := round_mono_real hdiv
  unfold code
  exact max_le_max le_rfl (min_le_min le_rfl hr)

/-- The quantizer is monotone in the input. -/
theorem quantize_mono {Δ : ℝ} (hΔ : 0 < Δ) (kmin kmax : ℤ) :
    Monotone (quantize Δ kmin kmax) := by
  intro a b hab
  unfold quantize
  exact mul_le_mul_of_nonneg_left (Int.cast_le.mpr (code_mono hΔ _ _ hab)) hΔ.le

/-- Every in-range code point is a fixed point of the quantizer. -/
theorem quantize_codePoint {Δ : ℝ} (hΔ : 0 < Δ) {kmin kmax k : ℤ}
    (hlo : kmin ≤ k) (hhi : k ≤ kmax) :
    quantize Δ kmin kmax (Δ * (k : ℝ)) = Δ * (k : ℝ) := by
  have hdiv : (Δ * (k : ℝ)) / Δ = (k : ℝ) := mul_div_cancel_real Δ hΔ _
  unfold quantize code
  rw [hdiv, round_intCast, min_eq_right hhi, max_eq_right hlo]

/-- Inputs in the full-scale interval are never clipped. -/
theorem not_isClipped_of_mem_Icc {Δ : ℝ} (hΔ : 0 < Δ) {kmin kmax : ℤ} {x : ℝ}
    (hx : x ∈ Set.Icc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))) :
    ¬ IsClipped Δ kmin kmax x := by
  rw [Set.mem_Icc] at hx
  obtain ⟨hlo, hhi⟩ := hx
  have hy1 : (kmin : ℝ) ≤ x / Δ := by
    rw [le_div_iff₀ hΔ]
    linarith
  have hy2 : x / Δ ≤ (kmax : ℝ) := by
    rw [div_le_iff₀ hΔ]
    linarith
  have habs := abs_sub_round (x / Δ)
  rw [abs_le] at habs
  obtain ⟨hlo_abs, hhi_abs⟩ := habs
  show ¬ (round (x / Δ) < kmin ∨ kmax < round (x / Δ))
  rintro (hlt | hgt)
  · have h1 : round (x / Δ) + 1 ≤ kmin := by omega
    have hcast : (round (x / Δ) : ℝ) + 1 ≤ (kmin : ℝ) := by exact_mod_cast h1
    linarith
  · have h1 : kmax + 1 ≤ round (x / Δ) := by omega
    have hcast : (kmax : ℝ) + 1 ≤ (round (x / Δ) : ℝ) := by exact_mod_cast h1
    linarith

/-- Away from clipping the quantization error is at most `Δ / 2`. -/
theorem abs_quantize_sub_le_of_not_isClipped {Δ : ℝ} (hΔ : 0 < Δ) {kmin kmax : ℤ}
    {x : ℝ} (hx : ¬ IsClipped Δ kmin kmax x) :
    |quantize Δ kmin kmax x - x| ≤ Δ / 2 := by
  have hcode : code Δ kmin kmax x = round (x / Δ) :=
    code_eq_round_of_not_isClipped hx
  have habs := abs_sub_round (x / Δ)
  have hDx : Δ * (x / Δ) = x := mul_div_cancel₀ x (ne_of_gt hΔ)
  have h1 : Δ * (round (x / Δ) : ℝ) - x = Δ * ((round (x / Δ) : ℝ) - x / Δ) := by
    rw [mul_sub, hDx]
  unfold quantize
  rw [hcode, h1, abs_mul, abs_of_pos hΔ]
  have habs2 : |(round (x / Δ) : ℝ) - x / Δ| ≤ 1 / 2 := by
    rw [abs_sub_comm]
    exact habs
  calc Δ * |(round (x / Δ) : ℝ) - x / Δ| ≤ Δ * (1 / 2) :=
        mul_le_mul_of_nonneg_left habs2 hΔ.le
    _ = Δ / 2 := by ring

/-- In the full-scale interval the quantization error is at most `Δ / 2`. -/
theorem abs_quantize_sub_le_of_mem_Icc {Δ : ℝ} (hΔ : 0 < Δ) {kmin kmax : ℤ}
    {x : ℝ} (hx : x ∈ Set.Icc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))) :
    |quantize Δ kmin kmax x - x| ≤ Δ / 2 :=
  abs_quantize_sub_le_of_not_isClipped hΔ (not_isClipped_of_mem_Icc hΔ hx)

/-- The Mathlib interval projection `Set.projIcc` is a nearest point:
for real endpoints `a <= b`, `|x - (Set.projIcc a b hab x : ℝ)|` is at
most the distance from `x` to any point of `[a, b]`, so it is the
distance from `x` to that interval. -/
theorem abs_sub_projIcc_le {a b : ℝ} (hab : a ≤ b) (x : ℝ) {z : ℝ}
    (hz : z ∈ Set.Icc a b) :
    |x - (Set.projIcc a b hab x : ℝ)| ≤ |x - z| := by
  rw [Set.mem_Icc] at hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [Set.coe_projIcc]
  by_cases hx1 : x ≤ a
  · have hmin : min b x = x := min_eq_right (le_trans hx1 hab)
    have hmax : max a x = a := max_eq_left hx1
    rw [hmin, hmax]
    have hxz : x ≤ z := le_trans hx1 hz1
    rw [abs_of_nonpos (sub_nonpos.mpr hx1), abs_of_nonpos (sub_nonpos.mpr hxz)]
    linarith
  · have hx1' : a < x := lt_of_not_ge hx1
    by_cases hx2 : b ≤ x
    · have hmin : min b x = b := min_eq_left hx2
      have hmax : max a b = b := max_eq_right hab
      rw [hmin, hmax]
      have hzx : z ≤ x := le_trans hz2 hx2
      rw [abs_of_nonneg (sub_nonneg.mpr hx2), abs_of_nonneg (sub_nonneg.mpr hzx)]
      linarith
    · have hx2' : x < b := lt_of_not_ge hx2
      have hmin : min b x = x := min_eq_right (le_of_lt hx2')
      have hmax : max a x = x := max_eq_right (le_of_lt hx1')
      rw [hmin, hmax, sub_self, abs_zero]
      exact abs_nonneg _

/-- Quantizing an input agrees with quantizing its projection onto
the full-scale interval. -/
theorem quantize_eq_quantize_projIcc {Δ : ℝ} (hΔ : 0 < Δ) {kmin kmax : ℤ}
    (hk : kmin ≤ kmax) (x : ℝ) :
    quantize Δ kmin kmax x
      = quantize Δ kmin kmax
          (Set.projIcc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))
            (fullScale_le hΔ hk) x : ℝ) := by
  have hle : Δ * (kmin : ℝ) ≤ Δ * (kmax : ℝ) := fullScale_le hΔ hk
  have hcode_a : code Δ kmin kmax (Δ * (kmin : ℝ)) = kmin := by
    unfold code
    rw [mul_div_cancel_real Δ hΔ _, round_intCast, min_eq_right hk,
      max_eq_right le_rfl]
  have hcode_b : code Δ kmin kmax (Δ * (kmax : ℝ)) = kmax := by
    unfold code
    rw [mul_div_cancel_real Δ hΔ _, round_intCast, min_eq_left le_rfl,
      max_eq_right hk]
  have hmem := code_mem_Icc hk Δ x
  rw [Set.mem_Icc] at hmem
  obtain ⟨hlo_code, hhi_code⟩ := hmem
  have hcode_eq :
      code Δ kmin kmax x = code Δ kmin kmax (Set.projIcc (Δ * (kmin : ℝ))
        (Δ * (kmax : ℝ)) (fullScale_le hΔ hk) x : ℝ) := by
    by_cases hx1 : x ≤ Δ * (kmin : ℝ)
    · have hclamp : (Set.projIcc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))
          (fullScale_le hΔ hk) x : ℝ) = Δ * (kmin : ℝ) := by
        rw [Set.coe_projIcc, min_eq_right (le_trans hx1 hle), max_eq_left hx1]
      rw [hclamp, hcode_a]
      have hle1 : code Δ kmin kmax x ≤ code Δ kmin kmax (Δ * (kmin : ℝ)) :=
        code_mono hΔ kmin kmax hx1
      rw [hcode_a] at hle1
      exact le_antisymm hle1 hlo_code
    · have hx1' : Δ * (kmin : ℝ) < x := lt_of_not_ge hx1
      by_cases hx2 : Δ * (kmax : ℝ) ≤ x
      · have hclamp : (Set.projIcc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))
            (fullScale_le hΔ hk) x : ℝ) = Δ * (kmax : ℝ) := by
          rw [Set.coe_projIcc, min_eq_left hx2, max_eq_right hle]
        rw [hclamp, hcode_b]
        have hle2 : code Δ kmin kmax (Δ * (kmax : ℝ)) ≤ code Δ kmin kmax x :=
          code_mono hΔ kmin kmax hx2
        rw [hcode_b] at hle2
        exact le_antisymm hhi_code hle2
      · have hclamp : (Set.projIcc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))
            (fullScale_le hΔ hk) x : ℝ) = x := by
          rw [Set.coe_projIcc, min_eq_right (le_of_lt (lt_of_not_ge hx2)),
            max_eq_right (le_of_lt hx1')]
        rw [hclamp]
  unfold quantize
  rw [hcode_eq]

/-- For every input, the quantization error is at most the distance to the
full-scale interval plus `Δ / 2`. -/
theorem abs_quantize_sub_le {Δ : ℝ} (hΔ : 0 < Δ) {kmin kmax : ℤ}
    (hk : kmin ≤ kmax) (x : ℝ) :
    |quantize Δ kmin kmax x - x|
      ≤ |x - (Set.projIcc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))
            (fullScale_le hΔ hk) x : ℝ)| + Δ / 2 := by
  have heq := quantize_eq_quantize_projIcc hΔ hk x
  have hmem : (Set.projIcc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))
      (fullScale_le hΔ hk) x : ℝ)
      ∈ Set.Icc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ)) :=
    (Set.projIcc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ)) (fullScale_le hΔ hk) x).2
  have hbound := abs_quantize_sub_le_of_mem_Icc hΔ hmem
  have htri := abs_sub_le_mid (quantize Δ kmin kmax (Set.projIcc (Δ * (kmin : ℝ))
      (Δ * (kmax : ℝ)) (fullScale_le hΔ hk) x : ℝ))
    (Set.projIcc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))
      (fullScale_le hΔ hk) x : ℝ) x
  rw [abs_sub_comm (Set.projIcc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))
    (fullScale_le hΔ hk) x : ℝ) x] at htri
  rw [heq]
  linarith

/-- The roadmap contract for the saturating round-half-up quantizer:
monotonicity, the in-range `Δ / 2` error bound, and the global
distance-plus-`Δ / 2` error bound. -/
theorem quantize_correct {Δ : ℝ} (hΔ : 0 < Δ) {kmin kmax : ℤ}
    (hk : kmin ≤ kmax) :
    Monotone (quantize Δ kmin kmax)
      ∧ (∀ x ∈ Set.Icc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ)),
          |quantize Δ kmin kmax x - x| ≤ Δ / 2)
      ∧ (∀ x : ℝ, |quantize Δ kmin kmax x - x|
          ≤ |x - (Set.projIcc (Δ * (kmin : ℝ)) (Δ * (kmax : ℝ))
                (fullScale_le hΔ hk) x : ℝ)| + Δ / 2) := by
  exact ⟨quantize_mono hΔ _ _, fun x hx => abs_quantize_sub_le_of_mem_Icc hΔ hx,
    fun x => abs_quantize_sub_le hΔ hk x⟩

set_option linter.unusedVariables false in
/-- For `1 <= w`, the signed `w`-bit code range is nonempty in the right
order. Width zero is rejected by the hypothesis. -/
theorem signedMinCode_le_signedMaxCode {w : ℕ} (hw : 1 ≤ w) :
    signedMinCode w ≤ signedMaxCode w := by
  unfold signedMinCode signedMaxCode
  have hpos : (0 : ℤ) < (2 : ℤ) ^ (w - 1) := pow_pos (by norm_num) _
  omega

/-- A signed `w`-bit code range (`1 <= w`) contains exactly `2 ^ w` codes. -/
theorem signedMaxCode_sub_signedMinCode_add_one {w : ℕ} (hw : 1 ≤ w) :
    signedMaxCode w - signedMinCode w + 1 = (2 : ℤ) ^ w := by
  unfold signedMinCode signedMaxCode
  have hw1 : w - 1 + 1 = w := Nat.sub_add_cancel hw
  have hpow : (2 : ℤ) ^ (w - 1 + 1) = (2 : ℤ) ^ (w - 1) * 2 := pow_succ _ _
  rw [hw1] at hpow
  rw [hpow]
  ring

set_option linter.unusedVariables false in
/-- The in-range `Δ / 2` bound instantiated to signed `w`-bit codes
(`1 <= w`). -/
theorem abs_quantize_signed_sub_le_of_mem_Icc {Δ : ℝ} (hΔ : 0 < Δ) {w : ℕ}
    (hw : 1 ≤ w) {x : ℝ}
    (hx : x ∈ Set.Icc (Δ * (signedMinCode w : ℝ)) (Δ * (signedMaxCode w : ℝ))) :
    |quantize Δ (signedMinCode w) (signedMaxCode w) x - x| ≤ Δ / 2 := by
  exact abs_quantize_sub_le_of_mem_Icc hΔ hx

end MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp
