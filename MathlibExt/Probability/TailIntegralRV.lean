/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RegularVariation
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# Corrected regularly-varying tail integral

For a probability measure `μ` on `ℝ` whose combined tail is regularly varying
of index `-α` with `0 < α < 1` and which has tail balance `p`, the first-moment
tail integral satisfies

  `(∫ y in Ioc 0 (c * x), y ∂μ) / (x * combinedTail μ x) → p * α * c ^ (1 - α) / (1 - α)`.

## Source and statement correction

Source: `v1/Atlas/TheoryOfProbability/code/RegularVariation.lean`,
`regularlyVarying_tail_integral`, left unproved in v1. v1 states it for
`0 < α < 2`, `α ≠ 1`, which is false for `α > 1`: for the Pareto tail
`P(|X| > x) = x ^ (-α)` with `α > 1`, the numerator tends to the finite
positive mean `E[X ^+]` while the denominator `x * combinedTail μ x`
tends to `0`, so the ratio diverges to `+∞` (formalized in the test file),
whereas v1's constant `p * α * c ^ (1 - α) / (1 - α)` is negative when
`α > 1`. For `α = 1` the ratio diverges logarithmically. This batch ports
the corrected statement for `0 < α < 1`.

The module uses the canonical `RegularVariation` predicates, strict left/right
and combined tails, and guarded tail balance. The strict left tail is
`μ(Iio(-x))`, so at nonnegative thresholds the combined tail is the real strict
absolute-tail mass. The earlier inclusive `Iic(-x)` representation counted
boundary atoms and is corrected here.

The proof uses eventual positivity in Potter's bound and Karamata's integral
theorem for antitone tails, the pinned Mathlib layer-cake API for the restricted
first moment, and tail balance. No global first moment or no-atoms assumption is
needed.

## Analytic proof references

The mathematical inputs are Potter's bounds and Karamata's integral theorem:
N. H. Bingham, C. M. Goldie and J. L. Teugels, *Regular Variation*, Cambridge
University Press, 1987, Theorems 1.5.6 and 1.5.11 (direct half), respectively.
Here the integral theorem is used with weight exponent `β = 0` and
`ρ = -α > -1`.

The adapted dyadic Lean development is inspectable in
`MathlibExt/Probability/RegularVariationKaramata.lean` at commit
`e3e3f8ecc896e5925ae9c2b5da576063df868e2e`: `potter_upper` (including its dyadic
lower-bound step) and `karamata_integral`. This module specializes the integral
argument to `β = 0`.
The pre-repair first-moment implementation is
`MathlibExt/Probability/TailIntegralRV.lean` at commit
`88d996e13e6af4f66f6ead91f7b47faf0835c402`. The current proof retains that
analytic argument while using the canonical variation and tail interfaces;
v1 itself supplies the statement, not a proof.

The old globally-positive slow-factor predicate differs from canonical eventual
positivity for a fixed factor. The existential regular-variation predicates can
still be equivalent by patching early factor values. This API/representation
repair does not claim strict generality of the main theorem from that factor
example; tail endpoint and zero-denominator corrections are recorded separately.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace MathlibExt.Probability.TailIntegralRV

open MathlibExt.Probability.RegularVariation

/-- Ratio form of the canonical regular-variation predicate. Positivity is only
needed eventually, as in the canonical definition. -/
private theorem rv_ratio_tendsto {T : ℝ → ℝ} {ρ : ℝ}
    (hT : IsRegularlyVarying T ρ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => T (c * x) / T x) atTop (𝓝 (c ^ ρ)) := by
  obtain ⟨L, hL, hEv⟩ := hT
  have hmul : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have hEv2 : ∀ᶠ x in atTop, T (c * x) = (c * x) ^ ρ * L (c * x) :=
    hmul.eventually hEv
  have hEq : ∀ᶠ x in atTop, T (c * x) / T x = c ^ ρ * (L (c * x) / L x) := by
    filter_upwards [hEv, hEv2, hL.1, eventually_gt_atTop (0 : ℝ)]
      with x hx hx2 hLpos hxpos
    have hLx : L x ≠ 0 := ne_of_gt hLpos
    have hxr : x ^ ρ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hxpos ρ)
    rw [hx, hx2, Real.mul_rpow hc.le hxpos.le]
    field_simp
  refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm hEq) ?_
  have h := (hL.2 c hc).const_mul (c ^ ρ)
  simpa using h

/-- **Potter's lower bound** for antitone functions with a ratio limit: for every
`δ > 0` there are `D > 0` and `Y` such that `D * x ^ (ρ - δ) ≤ W x` for all
`x ≥ Y`. The proof chains the ratio limit at scale `2`. -/
private theorem potter_lower {W : ℝ → ℝ} {ρ : ℝ}
    (hW : Antitone W)
    (hpos : ∀ᶠ x in atTop, 0 < W x)
    (hratio : ∀ c : ℝ, 0 < c → Tendsto (fun x => W (c * x) / W x) atTop (𝓝 (c ^ ρ)))
    (hρ : ρ < 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : ℝ, ∃ Y : ℝ, 0 < D ∧ 0 < Y ∧ ∀ x ≥ Y, D * x ^ (ρ - δ) ≤ W x := by
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, ∀ x ≥ Y₀, 0 < W x := eventually_atTop.mp hpos
  set s := (2 : ℝ) ^ (ρ - δ / 2) with hsdef
  have hspos : 0 < s := Real.rpow_pos_of_pos (by norm_num) _
  have hslt : s < (2 : ℝ) ^ ρ :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  obtain ⟨Y₁, hY₁⟩ :=
    (Metric.tendsto_atTop.mp (hratio 2 (by norm_num))) ((2 : ℝ) ^ ρ - s) (by linarith)
  set Y := max (max Y₀ Y₁) 1 with hYdef
  have hYpos : 0 < Y := lt_max_iff.mpr (Or.inr one_pos)
  have hY0le : Y₀ ≤ Y := by
    calc Y₀ ≤ max Y₀ Y₁ := le_max_left _ _
      _ ≤ max (max Y₀ Y₁) 1 := le_max_left _ _
  have hY1le : Y₁ ≤ Y := by
    calc Y₁ ≤ max Y₀ Y₁ := le_max_right _ _
      _ ≤ max (max Y₀ Y₁) 1 := le_max_left _ _
  have hWpos : ∀ t ≥ Y, 0 < W t := fun t ht => hY₀ t (le_trans hY0le ht)
  have hstep : ∀ y ≥ Y, s ≤ W (2 * y) / W y := by
    intro y hy
    have h := hY₁ y (le_trans hY1le hy)
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.1]
  have hchain : ∀ k : ℕ, ∀ y ≥ Y, s ^ k * W y ≤ W ((2 : ℝ) ^ k * y) := by
    intro k
    induction k with
    | zero => intro y hy; simp
    | succ k ih =>
      intro y hy
      have harg : (2 : ℝ) ^ k * y ≥ Y := by
        calc Y ≤ y := hy
          _ = 1 * y := (one_mul y).symm
          _ ≤ (2 : ℝ) ^ k * y :=
            mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num))
              (le_of_lt (lt_of_lt_of_le hYpos hy))
      have h1 : s ^ (k + 1) * W y = s * (s ^ k * W y) := by rw [pow_succ]; ring
      rw [h1]
      calc s * (s ^ k * W y) ≤ s * W ((2 : ℝ) ^ k * y) :=
            mul_le_mul_of_nonneg_left (ih y hy) hspos.le
        _ ≤ W (2 * ((2 : ℝ) ^ k * y)) := by
            have h2 := hstep ((2 : ℝ) ^ k * y) harg
            rw [le_div_iff₀ (hWpos _ harg)] at h2
            exact h2
        _ = W ((2 : ℝ) ^ (k + 1) * y) := by
            congr 1
            rw [pow_succ]
            ring
  set D := W Y * s / Y ^ (ρ - δ) with hDdef
  have hDpos : 0 < D :=
    div_pos (mul_pos (hWpos Y le_rfl) hspos) (Real.rpow_pos_of_pos hYpos _)
  refine ⟨D, Y, hDpos, hYpos, ?_⟩
  intro x hx
  have hxY : (1 : ℝ) ≤ x / Y := by
    rw [le_div_iff₀ hYpos]
    simpa using hx
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hxY (show (1 : ℝ) < 2 by norm_num)
  have hyk_le : (2 : ℝ) ^ k * Y ≤ x := by
    have h := (le_div_iff₀ hYpos).mp hk1
    linarith [h]
  have hWx : W ((2 : ℝ) ^ (k + 1) * Y) ≤ W x := by
    apply hW
    have h := (div_lt_iff₀ hYpos).mp hk2
    linarith [h]
  have hchaink : s ^ (k + 1) * W Y ≤ W ((2 : ℝ) ^ (k + 1) * Y) :=
    hchain (k + 1) Y le_rfl
  have hkey : ((2 : ℝ) ^ k) ^ (ρ - δ) ≤ s ^ k := by
    have e1 : ((2 : ℝ) ^ k) ^ (ρ - δ) = (2 : ℝ) ^ ((k : ℝ) * (ρ - δ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) k,
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (k : ℝ) (ρ - δ)).symm]
    have e2 : s ^ k = (2 : ℝ) ^ ((k : ℝ) * (ρ - δ / 2)) := by
      rw [hsdef, ← Real.rpow_natCast ((2 : ℝ) ^ (ρ - δ / 2)) k,
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (ρ - δ / 2) (k : ℝ)).symm]
      congr 1
      ring
    rw [e1, e2]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hk0, hδ, hρ]
  calc D * x ^ (ρ - δ)
      ≤ D * (((2 : ℝ) ^ k * Y) ^ (ρ - δ)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) hyk_le (by linarith)) hDpos.le
    _ = W Y * s * ((2 : ℝ) ^ k) ^ (ρ - δ) := by
          rw [hDdef, Real.mul_rpow (by positivity) hYpos.le]
          field_simp
    _ ≤ W Y * s * s ^ k := by
          apply mul_le_mul_of_nonneg_left hkey
          exact mul_nonneg (hWpos Y le_rfl).le hspos.le
    _ = s ^ (k + 1) * W Y := by rw [pow_succ]; ring
    _ ≤ W x := le_trans hchaink hWx

/-- **Potter's upper bound** for antitone functions with a ratio limit: for every
`δ > 0` there are `C > 0` and `Y` such that `W (x * u) / W x ≤ C * u ^ (ρ - δ)`
for all `x ≥ Y` and `u ∈ (0, 1]`. The proof chains the ratio limit at the
dyadic scale `1 / 2`, with the small-`u` case handled by `potter_lower`. -/
private theorem potter_upper {W : ℝ → ℝ} {ρ : ℝ}
    (hW : Antitone W) (hWb : ∃ B, ∀ t, W t ≤ B)
    (hpos : ∀ᶠ x in atTop, 0 < W x)
    (hratio : ∀ c : ℝ, 0 < c → Tendsto (fun x => W (c * x) / W x) atTop (𝓝 (c ^ ρ)))
    (hρ : ρ < 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∃ Y : ℝ, 0 < C ∧ 0 < Y ∧ ∀ x ≥ Y, ∀ u ∈ Set.Ioc 0 1,
      W (x * u) / W x ≤ C * u ^ (ρ - δ) := by
  obtain ⟨B, hB⟩ := hWb
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, ∀ x ≥ Y₀, 0 < W x := eventually_atTop.mp hpos
  obtain ⟨D, Y₂, hDpos, hY₂pos, hlow⟩ :=
    potter_lower hW hpos hratio hρ (δ := δ / 2) (half_pos hδ)
  have hBpos : 0 < B := by
    have h := hY₀ Y₀ le_rfl
    linarith [hB Y₀]
  -- dyadic half-step bound
  set q := (2 : ℝ) ^ (-ρ + δ) with hqdef
  have hqpos : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have h12 : ((1 : ℝ) / 2) ^ ρ = (2 : ℝ) ^ (-ρ) := by
    have h1 : ((1 : ℝ) / 2) = (2 : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
      norm_num
    rw [h1, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hε : 0 < q - ((1 : ℝ) / 2) ^ ρ := by
    rw [h12]
    exact sub_pos.mpr (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith))
  obtain ⟨Y₁, hY₁⟩ :=
    (Metric.tendsto_atTop.mp (hratio (1 / 2) (by norm_num))) _ hε
  set Y := max (max (max Y₀ Y₁) Y₂) 1 with hYdef
  have hYpos : 0 < Y := lt_max_iff.mpr (Or.inr one_pos)
  have hY0le : Y₀ ≤ Y := by
    calc Y₀ ≤ max Y₀ Y₁ := le_max_left _ _
      _ ≤ max (max Y₀ Y₁) Y₂ := le_max_left _ _
      _ ≤ max (max (max Y₀ Y₁) Y₂) 1 := le_max_left _ _
  have hY1le : Y₁ ≤ Y := by
    calc Y₁ ≤ max Y₀ Y₁ := le_max_right _ _
      _ ≤ max (max Y₀ Y₁) Y₂ := le_max_left _ _
      _ ≤ max (max (max Y₀ Y₁) Y₂) 1 := le_max_left _ _
  have hY2le : Y₂ ≤ Y := by
    calc Y₂ ≤ max (max Y₀ Y₁) Y₂ := le_max_right _ _
      _ ≤ max (max (max Y₀ Y₁) Y₂) 1 := le_max_left _ _
  have hWpos : ∀ t ≥ Y, 0 < W t := fun t ht => hY₀ t (le_trans hY0le ht)
  have hstep_half : ∀ y ≥ Y, W (y / 2) / W y ≤ q := by
    intro y hy
    have h := hY₁ y (le_trans hY1le hy)
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    have heq : (1 / 2 : ℝ) * y = y / 2 := by ring
    rw [heq] at h
    linarith [h.2, hε]
  have hchain_half : ∀ m : ℕ, ∀ x : ℝ, (∀ j ≤ m, Y ≤ x / (2 : ℝ) ^ j) →
      W (x / (2 : ℝ) ^ m) ≤ q ^ m * W x := by
    intro m
    induction m with
    | zero => intro x _; simp
    | succ m ih =>
      intro x hx
      have harg : Y ≤ x / (2 : ℝ) ^ m := hx m (Nat.le_succ m)
      have h1 : x / (2 : ℝ) ^ (m + 1) = (x / (2 : ℝ) ^ m) / 2 := by
        rw [pow_succ]; field_simp
      rw [h1]
      have h2 : W ((x / (2 : ℝ) ^ m) / 2) ≤ q * W (x / (2 : ℝ) ^ m) := by
        have h3 := hstep_half _ harg
        rw [div_le_iff₀ (hWpos _ harg)] at h3
        linarith [h3]
      calc W ((x / (2 : ℝ) ^ m) / 2) ≤ q * W (x / (2 : ℝ) ^ m) := h2
        _ ≤ q * (q ^ m * W x) :=
            mul_le_mul_of_nonneg_left (ih x (fun j hj => hx j (Nat.le_succ_of_le hj))) hqpos.le
        _ = q ^ (m + 1) * W x := by rw [pow_succ]; ring
  set C' := B / (D * Y ^ (ρ - δ / 2)) with hC'def
  have hC'pos : 0 < C' :=
    div_pos hBpos (mul_pos hDpos (Real.rpow_pos_of_pos hYpos _))
  set C := max q C' with hCdef
  have hCpos : 0 < C := lt_max_iff.mpr (Or.inl hqpos)
  refine ⟨C, Y, hCpos, hYpos, ?_⟩
  intro x hx u hu
  obtain ⟨hu0, hu1⟩ := hu
  have hxpos : 0 < x := lt_of_lt_of_le hYpos hx
  have hWx : 0 < W x := hWpos x hx
  by_cases hcase : Y ≤ x * u
  · -- Case A: `x * u ≥ Y`, chain down dyadically from `x`.
    obtain ⟨m, hm1, hm2⟩ :=
      exists_nat_pow_near (show (1 : ℝ) ≤ 1 / u by
        rw [le_div_iff₀ hu0]; simpa using hu1) (show (1 : ℝ) < 2 by norm_num)
    set y := x / (2 : ℝ) ^ m with hydef
    have hu2 : u * (2 : ℝ) ^ m ≤ 1 := by
      have h1 : (2 : ℝ) ^ m ≤ 1 / u := hm1
      rw [le_div_iff₀ hu0] at h1
      linarith [h1]
    have hyY : y ≥ Y := by
      rw [hydef]
      calc Y ≤ x * u := hcase
        _ ≤ x / (2 : ℝ) ^ m := by
            rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ m)]
            calc (x * u) * (2 : ℝ) ^ m = x * (u * (2 : ℝ) ^ m) := by ring
              _ ≤ x * 1 := mul_le_mul_of_nonneg_left hu2 hxpos.le
              _ = x := mul_one x
    have hxu_gt : y / 2 < x * u := by
      rw [hydef]
      have h1 : (2 : ℝ) ^ (-(m : ℝ)) < 2 * u := by
        have h2 : 1 / u < (2 : ℝ) ^ (m + 1) := hm2
        rw [div_lt_iff₀ hu0] at h2
        have h3 : (2 : ℝ) ^ (-(m : ℝ)) = 1 / (2 : ℝ) ^ m := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
          exact inv_eq_one_div _
        rw [h3, div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ m)]
        calc (1 : ℝ) < (2 : ℝ) ^ (m + 1) * u := by linarith [h2]
          _ = 2 * u * (2 : ℝ) ^ m := by rw [pow_succ]; ring
      have h2 : x / (2 : ℝ) ^ m / 2 = x * ((2 : ℝ) ^ (-(m : ℝ)) / 2) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
        field_simp
      rw [h2]
      apply mul_lt_mul_of_pos_left _ hxpos
      linarith [h1]
    have hWxu : W (x * u) ≤ W (y / 2) := hW (le_of_lt hxu_gt)
    have hWy : 0 < W y := hWpos y hyY
    have harg : ∀ j ≤ m, Y ≤ x / (2 : ℝ) ^ j := by
      intro j hj
      have h2 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ m :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
      calc Y ≤ y := hyY
        _ = x / (2 : ℝ) ^ m := rfl
        _ ≤ x / (2 : ℝ) ^ j := by
          apply div_le_div_of_nonneg_left hxpos.le (by positivity) h2
    have hchain : W y ≤ q ^ m * W x := hchain_half m x harg
    have h1 : W (x * u) ≤ q ^ (m + 1) * W x := by
      have hle : W (x * u) / W y ≤ q := by
        calc W (x * u) / W y ≤ W (y / 2) / W y :=
              div_le_div_of_nonneg_right hWxu hWy.le
          _ ≤ q := hstep_half y hyY
      have h2 : W (x * u) ≤ q * W y := by
        rw [div_le_iff₀ hWy] at hle
        linarith [hle]
      calc W (x * u) ≤ q * W y := h2
        _ ≤ q * (q ^ m * W x) := mul_le_mul_of_nonneg_left hchain hqpos.le
        _ = q ^ (m + 1) * W x := by rw [pow_succ]; ring
    have hkey : q ^ m ≤ u ^ (ρ - δ) := by
      have e1 : q ^ m = ((2 : ℝ) ^ m) ^ (-ρ + δ) := by
        rw [hqdef, ← Real.rpow_natCast ((2 : ℝ) ^ (-ρ + δ)) m,
          (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (-ρ + δ) (m : ℝ)).symm,
          ← Real.rpow_natCast (2 : ℝ) m,
          (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (m : ℝ) (-ρ + δ)).symm]
        congr 1
        ring
      have e2 : ((2 : ℝ) ^ m) ^ (-ρ + δ) = (((2 : ℝ) ^ m)⁻¹) ^ (ρ - δ) := by
        rw [show (-ρ + δ) = -(ρ - δ) by ring,
          Real.rpow_neg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ m),
          Real.inv_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ m)]
      have hle2 : (((2 : ℝ) ^ m)⁻¹) ^ (ρ - δ) ≤ u ^ (ρ - δ) := by
        apply Real.rpow_le_rpow_of_nonpos hu0 _ (by linarith : ρ - δ ≤ 0)
        have h : u ≤ 1 / (2 : ℝ) ^ m := (le_div_iff₀ (by positivity)).mpr hu2
        rwa [one_div] at h
      rw [e1, e2]
      exact hle2
    calc W (x * u) / W x ≤ q ^ (m + 1) := by
          rw [div_le_iff₀ hWx]
          linarith [h1]
      _ = q * q ^ m := by rw [pow_succ]; ring
      _ ≤ q * u ^ (ρ - δ) := mul_le_mul_of_nonneg_left hkey hqpos.le
      _ ≤ C * u ^ (ρ - δ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hu0.le _)
  · -- Case B: `x * u < Y`, use boundedness above and `potter_lower` below.
    have hcase : x * u < Y := lt_of_not_ge hcase
    have hu' : u < Y / x := by
      rw [lt_div_iff₀ hxpos]
      calc u * x = x * u := by ring
        _ < Y := hcase
    have hlowx : D * x ^ (ρ - δ / 2) ≤ W x := hlow x (le_trans hY2le hx)
    have e1 : (Y / x) ^ (ρ - δ) * x ^ (ρ - δ / 2) = Y ^ (ρ - δ) * x ^ (δ / 2) := by
      rw [Real.div_rpow hYpos.le hxpos.le]
      have h3 : x ^ (ρ - δ / 2) / x ^ (ρ - δ) = x ^ (δ / 2) := by
        rw [← Real.rpow_sub hxpos]; congr 1; ring
      rw [div_mul_eq_mul_div, mul_div_assoc, h3]
    have h4 : Y ^ (δ / 2) ≤ x ^ (δ / 2) :=
      Real.rpow_le_rpow hYpos.le hx.le (by linarith : (0 : ℝ) ≤ δ / 2)
    have hle : Y ^ (ρ - δ / 2) ≤ (Y / x) ^ (ρ - δ) * x ^ (ρ - δ / 2) := by
      rw [e1, show (ρ - δ / 2) = (ρ - δ) + δ / 2 by ring, Real.rpow_add hYpos]
      exact mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hYpos.le _)
    have hlt : (Y / x) ^ (ρ - δ) < u ^ (ρ - δ) :=
      Real.rpow_lt_rpow_of_neg hu0 hu' (by linarith : ρ - δ < 0)
    have h2 : Y ^ (ρ - δ / 2) < u ^ (ρ - δ) * x ^ (ρ - δ / 2) :=
      lt_of_le_of_lt hle (mul_lt_mul_of_pos_right hlt (Real.rpow_pos_of_pos hxpos _))
    have h3 : B < C' * u ^ (ρ - δ) * W x := by
      have h5 : B = C' * (D * Y ^ (ρ - δ / 2)) := by
        rw [hC'def, div_mul_cancel₀ _
          (mul_ne_zero (ne_of_gt hDpos) (ne_of_gt (Real.rpow_pos_of_pos hYpos _)))]
      rw [h5]
      calc C' * (D * Y ^ (ρ - δ / 2))
          < C' * (D * (u ^ (ρ - δ) * x ^ (ρ - δ / 2))) := by
            apply mul_lt_mul_of_pos_left _ hC'pos
            exact mul_lt_mul_of_pos_left h2 hDpos
        _ = C' * u ^ (ρ - δ) * (D * x ^ (ρ - δ / 2)) := by ring
        _ ≤ C' * u ^ (ρ - δ) * W x :=
            mul_le_mul_of_nonneg_left hlowx
              (mul_nonneg hC'pos.le (Real.rpow_nonneg hu0.le _))
    have h4 : W (x * u) / W x ≤ C' * u ^ (ρ - δ) := by
      rw [div_le_iff₀ hWx]
      exact le_of_lt (lt_of_le_of_lt (hB _) h3)
    calc W (x * u) / W x ≤ C' * u ^ (ρ - δ) := h4
      _ ≤ C * u ^ (ρ - δ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hu0.le _)

/-- **Karamata's integral theorem** (first-moment form) for antitone functions with
a ratio limit. If `W` is antitone, nonnegative, bounded, eventually positive and
`W (c * x) / W x → c ^ ρ` for every `c > 0`, with `-1 < ρ < 0`, then
`(∫ t in (0:ℝ)..x, W t) / (x * W x) → 1 / (1 + ρ)`.
The proof substitutes `t = x * u` and applies dominated convergence with
Potter's bound as the dominator. -/
private theorem karamata_integral_zero {W : ℝ → ℝ} {ρ : ℝ}
    (hW : Antitone W) (hWnn : ∀ t, 0 ≤ W t) (hWb : ∃ B, ∀ t, W t ≤ B)
    (hpos : ∀ᶠ x in atTop, 0 < W x)
    (hratio : ∀ c : ℝ, 0 < c → Tendsto (fun x => W (c * x) / W x) atTop (𝓝 (c ^ ρ)))
    (hρ : ρ < 0) (hρ1 : -1 < ρ) :
    Tendsto (fun x => (∫ t in (0:ℝ)..x, W t) / (x * W x))
      atTop (𝓝 (1 / (1 + ρ))) := by
  obtain ⟨C, Y, hC, hYpos, hPotter⟩ :=
    potter_upper hW hWb hpos hratio hρ (δ := (1 + ρ) / 2) (by linarith)
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, ∀ x ≥ Y₀, 0 < W x := eventually_atTop.mp hpos
  set Y' := max Y Y₀ with hY'def
  have hY'pos : 0 < Y' := lt_of_lt_of_le hYpos (le_max_left _ _)
  have hWpos : ∀ x ≥ Y', 0 < W x := fun x hx => hY₀ x (le_trans (le_max_right _ _) hx)
  have hPotter' : ∀ x ≥ Y', ∀ u ∈ Set.Ioc 0 1,
      W (x * u) / W x ≤ C * u ^ (ρ - (1 + ρ) / 2) :=
    fun x hx u hu => hPotter x (le_trans (le_max_left _ _) hx) u hu
  have hEq : ∀ᶠ x in atTop,
      (∫ t in (0:ℝ)..x, W t) / (x * W x)
        = ∫ u in (0:ℝ)..1, (W (x * u) / W x) := by
    filter_upwards [eventually_ge_atTop Y'] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le hY'pos hx
    have hWx : 0 < W x := hWpos x hx
    have h3 : (∫ u in (0:ℝ)..1, (W (x * u) / W x))
        = (∫ u in (0:ℝ)..1, W (x * u)) / W x :=
      intervalIntegral.integral_div _ _
    have hsub : ∫ t in (0:ℝ)..x, W t
        = x * ∫ u in (0:ℝ)..1, W (x * u) := by
      have h0 : ∫ u in (0:ℝ)..1, W (x * u)
          = x⁻¹ * ∫ t in (0:ℝ)..x, W t := by
        have h0' := intervalIntegral.integral_comp_mul_left (fun t => W t)
          (a := (0:ℝ)) (b := (1:ℝ)) hxpos.ne'
        simpa using h0'
      rw [h0, ← mul_assoc, mul_inv_cancel₀ hxpos.ne', one_mul]
    rw [hsub]
    have hxp : x ≠ 0 := ne_of_gt hxpos
    rw [mul_div_mul_left _ _ hxp]
    exact h3.symm
  -- dominated convergence for the rescaled integrand
  set δ' := (1 + ρ) / 2 with hδ'def
  have hδ'pos : 0 < δ' := by linarith
  have hDCT : Tendsto (fun x => ∫ u in (0:ℝ)..1, (W (x * u) / W x))
      atTop (𝓝 (∫ u in (0:ℝ)..1, u ^ ρ)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun u => C * u ^ (ρ - δ'))
    · -- measurability of the rescaled integrand
      filter_upwards [eventually_ge_atTop Y'] with x hx
      have hmeas : Measurable (fun u => W (x * u) / W x) :=
        ((hW.measurable).comp (measurable_const_mul x)).div_const _
      exact (hmeas.aestronglyMeasurable).restrict
    · -- domination by Potter's bound
      filter_upwards [eventually_ge_atTop Y'] with x hx
      apply Filter.Eventually.of_forall
      intro u hu
      have huIoc : u ∈ Set.Ioc 0 1 := by
        simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hu
      have hu0 : 0 < u := huIoc.1
      have hWx : 0 < W x := hWpos x hx
      have hnn : 0 ≤ W (x * u) / W x := div_nonneg (hWnn _) hWx.le
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hPotter' x hx u huIoc
    · -- integrability of the dominator
      apply IntervalIntegrable.const_mul
      apply intervalIntegral.intervalIntegrable_rpow'
      show (-1 : ℝ) < ρ - δ'
      rw [hδ'def]
      linarith
    · -- pointwise convergence
      apply Filter.Eventually.of_forall
      intro u hu
      have huIoc : u ∈ Set.Ioc 0 1 := by
        simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hu
      have hu0 : 0 < u := huIoc.1
      have hlim : Tendsto (fun x => W (x * u) / W x) atTop (𝓝 (u ^ ρ)) :=
        (hratio u hu0).congr (fun x => by rw [mul_comm])
      exact hlim
  -- evaluate the limit integral
  have hInt : (∫ u in (0:ℝ)..1, u ^ ρ) = 1 / (1 + ρ) := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < ρ)), Real.one_rpow,
      Real.zero_rpow (ne_of_gt (by linarith : (0 : ℝ) < ρ + 1)), sub_zero]
    congr 1
    ring
  rw [hInt] at hDCT
  have hEq' : (fun x => ∫ u in (0:ℝ)..1, (W (x * u) / W x)) =ᶠ[atTop]
      (fun x => (∫ t in (0:ℝ)..x, W t) / (x * W x)) := Filter.EventuallyEq.symm hEq
  exact Filter.Tendsto.congr' hEq' hDCT

/-- Antitone bounded functions are interval-integrable. -/
theorem intervalIntegrable_of_antitone_bdd {W : ℝ → ℝ} (hW : Antitone W)
    (hWnn : ∀ t, 0 ≤ W t) (hWbdd : ∃ B, ∀ t, W t ≤ B) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable W volume a b := by
  obtain ⟨B, hB⟩ := hWbdd
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply Measure.integrableOn_of_bounded (measure_Ioc_lt_top.ne)
    ((hW.measurable).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (hWnn t)]
  exact hB t

/-- Layer-cake formula for the first moment on `(0, a]`: the integral of `y`
over `(0, a]` equals the integral of the right tail minus the endpoint
correction. -/
theorem layerCake_firstMoment {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) :
    ∫ y in Set.Ioc 0 a, y ∂μ
      = ∫ t in (0:ℝ)..a, (rightTail μ t - rightTail μ a) := by
  have hInt : Integrable (fun y : ℝ => y) (μ.restrict (Set.Ioc 0 a)) := by
    apply Measure.integrableOn_of_bounded (M := a) (measure_Ioc_lt_top.ne)
      continuous_id.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy0 : (0:ℝ) ≤ y := (Set.mem_Ioc.mp hy).1.le
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hy0] using (Set.mem_Ioc.mp hy).2
  have hNonneg : (0 : ℝ → ℝ) ≤ᵐ[μ.restrict (Set.Ioc 0 a)] (fun y : ℝ => y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact (Set.mem_Ioc.mp hy).1.le
  have hmeas : ∫ y, y ∂(μ.restrict (Set.Ioc 0 a))
      = ∫ t in Set.Ioi (0:ℝ), (μ.restrict (Set.Ioc 0 a)).real {y : ℝ | t < y} :=
    Integrable.integral_eq_integral_meas_lt hInt hNonneg
  rw [hmeas]
  have htrunc : ∫ t in Set.Ioi (0:ℝ), (μ.restrict (Set.Ioc 0 a)).real {y : ℝ | t < y} ∂volume
      = ∫ t in Set.Ioc 0 a, (μ.restrict (Set.Ioc 0 a)).real {y : ℝ | t < y} ∂volume := by
    apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Ioi
      (Set.Ioc_subset_Ioi_self)
    apply Filter.Eventually.of_forall
    intro t ht
    have ht0 : (0:ℝ) < t := ht.1
    have hta : a < t := by
      have hnot : t ∉ Set.Ioc 0 a := ht.2
      exact lt_of_not_ge (fun h => hnot ⟨ht0, h⟩)
    show ((μ.restrict (Set.Ioc 0 a)) {y : ℝ | t < y}).toReal = 0
    have hempty : {y : ℝ | t < y} ∩ Set.Ioc 0 a = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨h1, -, h2⟩
      linarith [hta]
    have hmeas0 : MeasurableSet {y : ℝ | t < y} :=
      measurableSet_lt measurable_const measurable_id
    rw [Measure.restrict_apply hmeas0, hempty]
    simp
  rw [htrunc, intervalIntegral.integral_of_le ha]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have ht0 : (0:ℝ) < t := (Set.mem_Ioc.mp ht).1
  have hta : t ≤ a := (Set.mem_Ioc.mp ht).2
  have hset : {y : ℝ | t < y} ∩ Set.Ioc 0 a = Set.Ioc t a := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith [ht0], h2⟩
  have hmeas2 : MeasurableSet {y : ℝ | t < y} :=
    measurableSet_lt measurable_const measurable_id
  show ((μ.restrict (Set.Ioc 0 a)) {y : ℝ | t < y}).toReal
      = (μ (Set.Ioi t)).toReal - (μ (Set.Ioi a)).toReal
  rw [Measure.restrict_apply hmeas2, hset]
  have hunion : μ (Set.Ioi t) = μ (Set.Ioc t a) + μ (Set.Ioi a) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hta]
    exact measure_union
      (Set.disjoint_left.mpr (fun y hy1 hy2 =>
        (not_le.mpr (Set.mem_Ioi.mp hy2)) (Set.mem_Ioc.mp hy1).2)) measurableSet_Ioi
  have hsub : μ (Set.Ioc t a) = μ (Set.Ioi t) - μ (Set.Ioi a) := by
    rw [hunion, ENNReal.add_sub_cancel_right (measure_ne_top _ _)]
  rw [hsub]
  exact ENNReal.toReal_sub_of_le (measure_mono (Set.Ioi_subset_Ioi hta)) (measure_ne_top _ _)

/-- **Corrected regularly-varying tail integral.** For a probability measure `μ`
on `ℝ` with regularly varying combined tail of index `-α`, `0 < α < 1`, and
tail balance `p`, the first-moment tail integral satisfies
`(∫ y in Ioc 0 (c * x), y ∂μ) / (x * combinedTail μ x) → p * α * c ^ (1 - α) / (1 - α)`. -/
theorem tailIntegral_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {p : ℝ} (hTB : HasTailBalance μ p)
    (hRV : IsRegularlyVarying (combinedTail μ) (-α)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => (∫ y in Set.Ioc 0 (c * x), y ∂μ) / (x * combinedTail μ x))
      atTop (𝓝 (p * α * c ^ (1 - α) / (1 - α))) := by
  obtain ⟨hp0, hp1, hTBpos, hbal⟩ := hTB
  have hCanti : Antitone (combinedTail μ) := combinedTail_antitone μ
  have hRanti : Antitone (rightTail μ) := rightTail_antitone μ
  have hCnn : ∀ t, 0 ≤ combinedTail μ t := fun t => combinedTail_nonneg μ t
  have hRnn : ∀ t, 0 ≤ rightTail μ t := fun t => rightTail_nonneg μ t
  have hCbdd : ∃ B, ∀ t, combinedTail μ t ≤ B := ⟨2, fun t => combinedTail_le_two μ t⟩
  have hRbdd : ∃ B, ∀ t, rightTail μ t ≤ B := ⟨1, fun t => rightTail_le_one μ t⟩
  have hCpos : ∀ᶠ x in atTop, 0 < combinedTail μ x := hRV.eventually_pos
  have hCratio : ∀ d : ℝ, 0 < d →
      Tendsto (fun x => combinedTail μ (d * x) / combinedTail μ x)
        atTop (𝓝 (d ^ (-α))) := fun d hd => rv_ratio_tendsto hRV hd
  have hCInt : ∀ a b : ℝ, a ≤ b → IntervalIntegrable (combinedTail μ) volume a b :=
    fun a b hab => intervalIntegrable_of_antitone_bdd hCanti hCnn hCbdd hab
  have hRInt : ∀ a b : ℝ, a ≤ b → IntervalIntegrable (rightTail μ) volume a b :=
    fun a b hab => intervalIntegrable_of_antitone_bdd hRanti hRnn hRbdd hab
  -- Karamata for the combined tail.
  have hK_C : Tendsto
      (fun x => (∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x))
      atTop (𝓝 (1 / (1 - α))) := by
    have h := karamata_integral_zero hCanti hCnn hCbdd hCpos hCratio (by linarith : (-α) < 0)
      (by linarith : -1 < -α)
    rw [show (1:ℝ) - α = 1 + -α by ring]
    exact h
  -- `x * combinedTail μ x → ∞` via Potter's lower bound.
  have hXCbdd : Tendsto (fun x => x * combinedTail μ x) atTop atTop := by
    obtain ⟨D, Y, hDpos, hYpos, hlow⟩ :=
      potter_lower hCanti hCpos hCratio (by linarith : (-α) < 0) (δ := (1 - α) / 2)
        (by linarith)
    have hle : ∀ᶠ x in atTop, D * x ^ ((1 - α) / 2) ≤ x * combinedTail μ x := by
      filter_upwards [eventually_ge_atTop Y] with x hx
      have hxpos : 0 < x := lt_of_lt_of_le hYpos hx
      have h1 := hlow x hx
      have e : x ^ ((1 - α) / 2) = x ^ (-α - (1 - α) / 2) * x := by
        have h := Real.rpow_add hxpos (-α - (1 - α) / 2) (1:ℝ)
        rw [Real.rpow_one] at h
        rw [← h]
        congr 1
        ring
      calc D * x ^ ((1 - α) / 2)
          = (D * x ^ (-α - (1 - α) / 2)) * x := by rw [e]; ring
        _ ≤ combinedTail μ x * x := mul_le_mul_of_nonneg_right h1 hxpos.le
        _ = x * combinedTail μ x := by ring
    have htop : Tendsto (fun x => D * x ^ ((1 - α) / 2)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith : (0:ℝ) < (1 - α) / 2)).const_mul_atTop hDpos
    exact tendsto_atTop_mono' atTop hle htop
  -- `c * c ^ (-α) = c ^ (1 - α)`, used for the scaled factors below.
  have hc_pow : c * c ^ (-α) = c ^ (1 - α) := by
    have h := Real.rpow_add hc (1:ℝ) (-α)
    rw [Real.rpow_one] at h
    rw [← h, show (1:ℝ) + -α = 1 - α by ring]
  -- Key sandwich: the integrated right tail has the same asymptotics as the
  -- integrated combined tail, scaled by the balance `p`.
  have key : Tendsto (fun x => (∫ t in (0:ℝ)..x, rightTail μ t) / (x * combinedTail μ x))
      atTop (𝓝 (p / (1 - α))) := by
    rw [Metric.tendsto_nhds]
    intro ε' hε'
    set ε := ε' * (1 - α) / 4 with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]
      exact div_pos (mul_pos hε' (by linarith)) (by norm_num)
    set δ₂ := ε' / (4 * (1 + ε)) with hδ₂def
    have hδ₂pos : 0 < δ₂ := by
      rw [hδ₂def]
      exact div_pos hε' (by positivity)
    have hδ₂le : δ₂ ≤ ε' / 4 := by
      rw [hδ₂def]
      exact div_le_div_of_nonneg_left hε'.le (by norm_num) (by linarith [hεpos])
    have hαne : (1:ℝ) - α ≠ 0 := by linarith
    have h1εne : (1:ℝ) + ε ≠ 0 := by linarith [hεpos]
    have hεL : ε * (1 / (1 - α)) = ε' / 4 := by
      rw [hεdef]
      field_simp
    have h1εδ₂ : (1 + ε) * δ₂ = ε' / 4 := by
      rw [hδ₂def]
      field_simp
    -- the threshold `T` where the balance ratio is within `ε` of `p`
    obtain ⟨T, hT0, hT⟩ :
        ∃ T, 0 ≤ T ∧ ∀ t ≥ T, |rightTail μ t / combinedTail μ t - p| < ε := by
      have h1 : ∀ᶠ t in atTop, |rightTail μ t / combinedTail μ t - p| < ε := by
        filter_upwards [(Metric.tendsto_nhds.mp hbal) ε hεpos] with t ht
        rwa [Real.dist_eq] at ht
      obtain ⟨T, hT⟩ := eventually_atTop.mp h1
      exact ⟨max T 0, le_max_right _ _, fun t ht => hT t (le_trans (le_max_left _ _) ht)⟩
    have hbounds : ∀ t ≥ T, (p - ε) * combinedTail μ t ≤ rightTail μ t ∧
        rightTail μ t ≤ (p + ε) * combinedTail μ t := by
      intro t ht
      have h := hT t ht
      by_cases hC : combinedTail μ t = 0
      · have hR : rightTail μ t = 0 := by
          have hle : rightTail μ t ≤ combinedTail μ t :=
            le_add_of_nonneg_right (leftTail_nonneg μ t)
          rw [hC] at hle
          exact le_antisymm hle (hRnn t)
        rw [hC, hR]
        constructor <;> simp
      · have hCpos' : 0 < combinedTail μ t :=
          lt_of_le_of_ne (hCnn t) (fun h => hC h.symm)
        have h1 : p - ε < rightTail μ t / combinedTail μ t := by
          have := (abs_lt.mp h).1
          linarith
        have h2 : rightTail μ t / combinedTail μ t < p + ε := by
          have := (abs_lt.mp h).2
          linarith
        constructor
        · exact (lt_div_iff₀ hCpos').mp h1 |>.le
        · exact (div_lt_iff₀ hCpos').mp h2 |>.le
    -- integral bounds at `x ≥ T`
    have hKev : ∀ᶠ x in atTop,
        |(∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x) - 1 / (1 - α)| < δ₂ := by
      filter_upwards [(Metric.tendsto_nhds.mp hK_C) δ₂ hδ₂pos] with x hx
      rwa [Real.dist_eq] at hx
    have hXev : ∀ᶠ x in atTop, 8 * T / ε' ≤ x * combinedTail μ x :=
      (tendsto_atTop.mp hXCbdd) (8 * T / ε')
    filter_upwards [eventually_ge_atTop (max T 1), hKev, hXev, hCpos] with x hxT hxK hxXC hxC
    have hxT' : T ≤ x := le_trans (le_max_left _ _) hxT
    have hx1 : (1:ℝ) ≤ x := le_trans (le_max_right _ _) hxT
    have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
    have hxCpos : 0 < x * combinedTail μ x := mul_pos hxpos hxC
    have hxCne : x * combinedTail μ x ≠ 0 := ne_of_gt hxCpos
    -- integral identities and bounds
    have hsplitR : (∫ t in (0:ℝ)..x, rightTail μ t)
        = (∫ t in (0:ℝ)..T, rightTail μ t) + (∫ t in (T:ℝ)..x, rightTail μ t) :=
      (intervalIntegral.integral_add_adjacent_intervals (hRInt 0 T hT0) (hRInt T x hxT')).symm
    have hsplitC : (∫ t in (0:ℝ)..x, combinedTail μ t)
        = (∫ t in (0:ℝ)..T, combinedTail μ t) + (∫ t in (T:ℝ)..x, combinedTail μ t) :=
      (intervalIntegral.integral_add_adjacent_intervals (hCInt 0 T hT0) (hCInt T x hxT')).symm
    have hRT : (∫ t in (0:ℝ)..T, rightTail μ t) ≤ T := by
      calc (∫ t in (0:ℝ)..T, rightTail μ t) ≤ ∫ t in (0:ℝ)..T, (1:ℝ) :=
            intervalIntegral.integral_mono_on hT0 (hRInt 0 T hT0) intervalIntegrable_const
              (fun t _ => rightTail_le_one μ t)
        _ = T := by rw [intervalIntegral.integral_const]; simp
    have hRTnn : 0 ≤ ∫ t in (0:ℝ)..T, rightTail μ t :=
      intervalIntegral.integral_nonneg hT0 (fun t _ => hRnn t)
    have hCT : (∫ t in (0:ℝ)..T, combinedTail μ t) ≤ 2 * T := by
      calc (∫ t in (0:ℝ)..T, combinedTail μ t) ≤ ∫ t in (0:ℝ)..T, (2:ℝ) :=
            intervalIntegral.integral_mono_on hT0 (hCInt 0 T hT0) intervalIntegrable_const
              (fun t _ => combinedTail_le_two μ t)
        _ = 2 * T := by
            rw [intervalIntegral.integral_const]
            simp only [sub_zero, smul_eq_mul]
            ring
    have hCTnn : 0 ≤ ∫ t in (0:ℝ)..T, combinedTail μ t :=
      intervalIntegral.integral_nonneg hT0 (fun t _ => hCnn t)
    have hTRhi : (∫ t in (T:ℝ)..x, rightTail μ t)
        ≤ (p + ε) * (∫ t in (T:ℝ)..x, combinedTail μ t) := by
      have h := intervalIntegral.integral_mono_on hxT' (hRInt T x hxT')
        ((hCInt T x hxT').const_mul (p + ε)) (fun t ht => (hbounds t ht.1).2)
      rwa [intervalIntegral.integral_const_mul] at h
    have hTRlo : (p - ε) * (∫ t in (T:ℝ)..x, combinedTail μ t)
        ≤ ∫ t in (T:ℝ)..x, rightTail μ t := by
      have h := intervalIntegral.integral_mono_on hxT' ((hCInt T x hxT').const_mul (p - ε))
        (hRInt T x hxT') (fun t ht => (hbounds t ht.1).1)
      rwa [intervalIntegral.integral_const_mul] at h
    have hTxxC : (∫ t in (T:ℝ)..x, combinedTail μ t)
        ≤ ∫ t in (0:ℝ)..x, combinedTail μ t := by
      rw [hsplitC]
      exact le_add_of_nonneg_left hCTnn
    have hupper : (∫ t in (0:ℝ)..x, rightTail μ t)
        ≤ T + (p + ε) * (∫ t in (0:ℝ)..x, combinedTail μ t) := by
      rw [hsplitR]
      calc (∫ t in (0:ℝ)..T, rightTail μ t) + (∫ t in (T:ℝ)..x, rightTail μ t)
          ≤ T + (p + ε) * (∫ t in (T:ℝ)..x, combinedTail μ t) := add_le_add hRT hTRhi
        _ ≤ T + (p + ε) * (∫ t in (0:ℝ)..x, combinedTail μ t) :=
            add_le_add le_rfl
              (mul_le_mul_of_nonneg_left hTxxC (by linarith [hp0, hεpos]))
    have hpeC : (p - ε) * (∫ t in (0:ℝ)..T, combinedTail μ t) ≤ 2 * T := by
      by_cases hpe : 0 ≤ p - ε
      · calc (p - ε) * (∫ t in (0:ℝ)..T, combinedTail μ t)
            ≤ 1 * (2 * T) := mul_le_mul (by linarith [hp1, hεpos]) hCT hCTnn (by norm_num)
          _ = 2 * T := by ring
      · have hpe' : p - ε < 0 := lt_of_not_ge hpe
        have hnonpos : (p - ε) * (∫ t in (0:ℝ)..T, combinedTail μ t) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_lt hpe') hCTnn
        linarith [hnonpos, hT0]
    have hlower : (p - ε) * (∫ t in (0:ℝ)..x, combinedTail μ t) - 2 * T
        ≤ ∫ t in (0:ℝ)..x, rightTail μ t := by
      rw [hsplitR]
      have h2 : (∫ t in (T:ℝ)..x, combinedTail μ t)
          = (∫ t in (0:ℝ)..x, combinedTail μ t) - (∫ t in (0:ℝ)..T, combinedTail μ t) := by
        rw [hsplitC]; ring
      calc (p - ε) * (∫ t in (0:ℝ)..x, combinedTail μ t) - 2 * T
          = (p - ε) * (∫ t in (0:ℝ)..x, combinedTail μ t)
              - (p - ε) * (∫ t in (0:ℝ)..T, combinedTail μ t)
              + ((p - ε) * (∫ t in (0:ℝ)..T, combinedTail μ t) - 2 * T) := by ring
        _ ≤ (p - ε) * (∫ t in (0:ℝ)..x, combinedTail μ t)
              - (p - ε) * (∫ t in (0:ℝ)..T, combinedTail μ t) := by linarith [hpeC]
        _ = (p - ε) * (∫ t in (T:ℝ)..x, combinedTail μ t) := by rw [h2]; ring
        _ ≤ ∫ t in (T:ℝ)..x, rightTail μ t := hTRlo
        _ ≤ (∫ t in (0:ℝ)..T, rightTail μ t) + (∫ t in (T:ℝ)..x, rightTail μ t) :=
            le_add_of_nonneg_left hRTnn
    -- ratio bounds
    have hTX : T / (x * combinedTail μ x) ≤ ε' / 8 := by
      by_cases hTz : T = 0
      · rw [hTz]
        simp only [zero_div]
        exact (div_pos hε' (by norm_num)).le
      · have hTpos : 0 < T := lt_of_le_of_ne hT0 (fun h => hTz h.symm)
        have h1 : T / (x * combinedTail μ x) ≤ T / (8 * T / ε') :=
          div_le_div_of_nonneg_left hTpos.le (div_pos (mul_pos (by norm_num) hTpos) hε') hxXC
        have h2 : T / (8 * T / ε') = ε' / 8 := by field_simp
        rw [h2] at h1
        exact h1
    have h2TX : 2 * T / (x * combinedTail μ x) ≤ ε' / 4 := by
      rw [mul_div_assoc]
      linarith [hTX]
    have hKi : (∫ t in (0:ℝ)..x, rightTail μ t) / (x * combinedTail μ x)
        ≤ (p + ε) * ((∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x))
          + ε' / 8 := by
      rw [div_le_iff₀ hxCpos]
      have hTX' : T ≤ ε' / 8 * (x * combinedTail μ x) := (div_le_iff₀ hxCpos).mp hTX
      calc (∫ t in (0:ℝ)..x, rightTail μ t)
          ≤ T + (p + ε) * (∫ t in (0:ℝ)..x, combinedTail μ t) := hupper
        _ ≤ ε' / 8 * (x * combinedTail μ x)
              + (p + ε) * (∫ t in (0:ℝ)..x, combinedTail μ t) := by linarith [hTX']
        _ = ((p + ε) * ((∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x))
              + ε' / 8) * (x * combinedTail μ x) := by
            field_simp
            ring
    have hLo : (p - ε) * ((∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x))
        - ε' / 4
        ≤ (∫ t in (0:ℝ)..x, rightTail μ t) / (x * combinedTail μ x) := by
      rw [le_div_iff₀ hxCpos]
      have h2T : 2 * T ≤ ε' / 4 * (x * combinedTail μ x) :=
        (div_le_iff₀ hxCpos).mp h2TX
      have h3 : ((p - ε) * ((∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x))
          - ε' / 4) * (x * combinedTail μ x)
          = (p - ε) * (∫ t in (0:ℝ)..x, combinedTail μ t)
            - ε' / 4 * (x * combinedTail μ x) := by
        field_simp
      rw [h3]
      linarith [hlower, h2T]
    -- the product error terms
    have hprod1 : (-(1 + ε)) * δ₂ ≤ (p - ε) *
        (((∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x)) - 1 / (1 - α)) := by
      have habs : |(p - ε) *
          (((∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x)) - 1 / (1 - α))|
          ≤ (1 + ε) * δ₂ := by
        rw [abs_mul]
        exact mul_le_mul (by { rw [abs_le]; constructor <;> linarith [hp0, hp1, hεpos] })
          (le_of_lt hxK) (abs_nonneg _) (by linarith [hεpos])
      have h := le_trans (neg_le_neg habs) (neg_abs_le _)
      rwa [← neg_mul] at h
    have hprod2 : (p + ε) *
        (((∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x)) - 1 / (1 - α))
        ≤ (1 + ε) * δ₂ := by
      calc (p + ε) *
            (((∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x)) - 1 / (1 - α))
          ≤ |(p + ε) *
            (((∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x)) - 1 / (1 - α))| :=
            le_abs_self _
        _ = (p + ε) *
            |((∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x)) - 1 / (1 - α)| := by
            rw [abs_mul, abs_of_nonneg (by linarith [hp0, hεpos])]
        _ ≤ (1 + ε) * δ₂ :=
            mul_le_mul (by linarith [hp1]) (le_of_lt hxK) (abs_nonneg _) (by linarith [hεpos])
    have hA1 : (p - ε) * ((∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x))
        ≥ (p - ε) * (1 / (1 - α)) - (1 + ε) * δ₂ := by linarith [hprod1]
    have hA2 : (p + ε) * ((∫ t in (0:ℝ)..x, combinedTail μ t) / (x * combinedTail μ x))
        ≤ (p + ε) * (1 / (1 - α)) + (1 + ε) * δ₂ := by linarith [hprod2]
    rw [Real.dist_eq, abs_lt]
    constructor
    · -- `-ε' < ratio - p / (1 - α)`
      have h1 : (p - ε) * (1 / (1 - α)) = p / (1 - α) - ε * (1 / (1 - α)) := by ring
      linarith [hLo, hA1, h1, hεL, h1εδ₂, hε']
    · -- `ratio - p / (1 - α) < ε'`
      have h2 : (p + ε) * (1 / (1 - α)) = p / (1 - α) + ε * (1 / (1 - α)) := by ring
      linarith [hKi, hA2, h2, hεL, h1εδ₂, hε']
  -- The `c`-scaled factors.
  have hB : Tendsto (fun x => c * (rightTail μ (c * x) / combinedTail μ x))
      atTop (𝓝 (p * c ^ (1 - α))) := by
    have h1 : Tendsto (fun x => rightTail μ (c * x) / combinedTail μ x)
        atTop (𝓝 (p * c ^ (-α))) := by
      have hbal_c : Tendsto (fun x => rightTail μ (c * x) / combinedTail μ (c * x))
          atTop (𝓝 p) :=
        hbal.comp (Filter.Tendsto.const_mul_atTop hc tendsto_id)
      have hC_c : Tendsto (fun x => combinedTail μ (c * x) / combinedTail μ x)
          atTop (𝓝 (c ^ (-α))) :=
        hCratio c hc
      have h := hbal_c.mul hC_c
      refine Filter.Tendsto.congr' ?_ h
      filter_upwards [(Filter.Tendsto.const_mul_atTop hc tendsto_id).eventually hCpos]
        with x hxCcx
      have hCcx : combinedTail μ (c * x) ≠ 0 := ne_of_gt hxCcx
      field_simp
    have hlimB : c * (p * c ^ (-α)) = p * c ^ (1 - α) := by
      calc c * (p * c ^ (-α)) = p * (c * c ^ (-α)) := by ring
        _ = p * c ^ (1 - α) := by rw [hc_pow]
    rw [← hlimB]
    exact h1.const_mul c
  have hCfactor : Tendsto (fun x => c * (combinedTail μ (c * x) / combinedTail μ x))
      atTop (𝓝 (c ^ (1 - α))) := by
    rw [← hc_pow]
    exact (hCratio c hc).const_mul c
  have hA : Tendsto (fun x => (∫ t in (0:ℝ)..(c * x), rightTail μ t) / (x * combinedTail μ x))
      atTop (𝓝 (p * c ^ (1 - α) / (1 - α))) := by
    have hkey_c : Tendsto
        (fun x => (∫ t in (0:ℝ)..(c * x), rightTail μ t) / ((c * x) * combinedTail μ (c * x)))
        atTop (𝓝 (p / (1 - α))) :=
      key.comp (Filter.Tendsto.const_mul_atTop hc tendsto_id)
    have hprod := hkey_c.mul hCfactor
    have hlim : p / (1 - α) * c ^ (1 - α) = p * c ^ (1 - α) / (1 - α) := by
      rw [div_mul_eq_mul_div]
    rw [hlim] at hprod
    refine Filter.Tendsto.congr' ?_ hprod
    filter_upwards [eventually_gt_atTop (0:ℝ),
      (Filter.Tendsto.const_mul_atTop hc tendsto_id).eventually hCpos, hCpos]
      with x hxpos hxCcx hxC
    have hCcx : combinedTail μ (c * x) ≠ 0 := ne_of_gt hxCcx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hcne : c ≠ 0 := ne_of_gt hc
    field_simp
  have hmain : Tendsto (fun x => (∫ y in Set.Ioc 0 (c * x), y ∂μ) / (x * combinedTail μ x))
      atTop (𝓝 (p * c ^ (1 - α) / (1 - α) - p * c ^ (1 - α))) := by
    have hEq : (fun x => (∫ y in Set.Ioc 0 (c * x), y ∂μ) / (x * combinedTail μ x))
        =ᶠ[atTop] (fun x => (∫ t in (0:ℝ)..(c * x), rightTail μ t) / (x * combinedTail μ x)
          - c * (rightTail μ (c * x) / combinedTail μ x)) := by
      filter_upwards [eventually_gt_atTop (0:ℝ), hCpos] with x hxpos hxC
      have hcx : 0 ≤ c * x := mul_nonneg hc.le hxpos.le
      have hxne : x ≠ 0 := ne_of_gt hxpos
      have hCxne : combinedTail μ x ≠ 0 := ne_of_gt hxC
      rw [layerCake_firstMoment hcx,
        intervalIntegral.integral_sub (hRInt 0 (c * x) hcx) intervalIntegrable_const,
        intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      field_simp
    exact Filter.Tendsto.congr' hEq.symm (hA.sub hB)
  have hfinal : p * c ^ (1 - α) / (1 - α) - p * c ^ (1 - α)
      = p * α * c ^ (1 - α) / (1 - α) := by
    have hne : (1:ℝ) - α ≠ 0 := by linarith
    field_simp
    ring
  rw [hfinal] at hmain
  exact hmain

#print axioms layerCake_firstMoment
#print axioms tailIntegral_tendsto

end MathlibExt.Probability.TailIntegralRV
