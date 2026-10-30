/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RegularVariation

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Regular variation and Karamata's integral theorem

Regularly varying tails and Karamata's theorem on the asymptotics of their
truncated moments. This module imports and extends the canonical
`MathlibExt.Probability.RegularVariation` predicates and strict tails. Slow
factors need only be eventually positive. The analytic results live in that
canonical namespace; no parallel variation or tail definitions are retained.
The old globally positive slow factors give an equivalent existential regular
predicate by patching early values, while the fixed slow predicates differ.

## Source

`v1/Atlas/TheoryOfProbability/code/RegularVariation.lean` states, for a
probability measure `μ` on `ℝ` whose combined tail is regularly varying of
index `-α` with `0 < α < 2`, that the truncated second moment satisfies

  `(∫ y in Icc (-x) x, y ^ 2 ∂μ) / (x ^ 2 * combinedTail μ x) → 2 / (2 - α)`.

That constant is wrong: for the Pareto tail `P(|X| > x) = x ^ (-α)` the
ratio tends to `α / (2 - α)` (see the test file). The companion file
`MathlibExt/Probability/TruncatedMomentRV.lean` proves the corrected
statement. The key analytic input, proved here, is Karamata's integral
theorem for monotone functions with regularly varying tails, whose proof
goes through Potter's bound, obtained from the ratio convergence at the
dyadic scales `1/2` and `2` together with monotonicity.

## Analytic proof references

The mathematical inputs are Potter's bounds and Karamata's integral theorem:
N. H. Bingham, C. M. Goldie and J. L. Teugels, *Regular Variation*, Cambridge
University Press, 1987, Theorems 1.5.6 and 1.5.11 (direct half), respectively.
Here the integral theorem has weight exponent `β` and `β + 1 + ρ > 0`.

The dyadic Lean proofs of `potter_upper` and `karamata_integral` are present in
this file at commit `e3e3f8ecc896e5925ae9c2b5da576063df868e2e`. The current
formalization retains that analytic argument while using the canonical
eventually-positive variation predicates. The v1 textbook-bank file cited
above supplies an unproved second-moment statement, not these analytic proofs.

## Main results

* `IsRegularlyVarying.ratio_tendsto`: if `T` is regularly varying of index
  `ρ` then `T (c * x) / T x → c ^ ρ`.
* `potter_upper`: Potter's bound for antitone functions with a ratio limit:
  `W (x * u) / W x ≤ C * u ^ (ρ - δ)` for `u ∈ (0, 1]`.
* `karamata_integral`: for `β ≥ 0` and `β + 1 + ρ > 0`,
  `(∫ t in (0)..x, t ^ β * W t) / (x ^ (β + 1) * W x) → 1 / (β + 1 + ρ)`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace MathlibExt.Probability.RegularVariation

/-- A regularly varying function has the expected ratio limit. -/
theorem IsRegularlyVarying.ratio_tendsto {T : ℝ → ℝ} {ρ : ℝ}
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
  have hEq' : (fun x => T (c * x) / T x) =ᶠ[atTop]
      (fun x => c ^ ρ * (L (c * x) / L x)) := hEq
  refine Filter.Tendsto.congr' hEq'.symm ?_
  have h := (hL.2 c hc).const_mul (c ^ ρ)
  simpa using h

/-- Telescoping product of ratios, for real-valued functions. -/
private theorem prod_range_div_telescope {f : ℕ → ℝ} {n : ℕ}
    (hf : ∀ i ≤ n, f i ≠ 0) :
    ∏ i ∈ Finset.range n, f (i + 1) / f i = f n / f 0 := by
  induction n with
  | zero =>
    rw [Finset.prod_range_zero]
    exact (div_self (hf 0 le_rfl)).symm
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (fun i hi => hf i (Nat.le_succ_of_le hi))]
    have h1 : f n ≠ 0 := hf n (Nat.le_succ n)
    have h2 : f 0 ≠ 0 := hf 0 (Nat.zero_le _)
    field_simp

/-- Monotonicity of finite products of nonnegative reals. -/
private theorem prod_le_prod_of_le {f g : ℕ → ℝ} {n : ℕ}
    (hf : ∀ i < n, 0 ≤ f i) (hfg : ∀ i < n, f i ≤ g i) :
    ∏ i ∈ Finset.range n, f i ≤ ∏ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have hprodg : 0 ≤ ∏ i ∈ Finset.range n, g i :=
      Finset.prod_nonneg (fun i hi =>
        le_trans (hf i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))
          (hfg i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))))
    exact mul_le_mul
      (ih (fun i hi => hf i (Nat.lt_succ_of_lt hi)) (fun i hi => hfg i (Nat.lt_succ_of_lt hi)))
      (hfg n (Nat.lt_succ_self n)) (hf n (Nat.lt_succ_self n)) hprodg

/-- **Potter's bound** for antitone functions with a ratio limit. If `W` is
antitone, bounded, eventually positive and `W (c * x) / W x → c ^ ρ` for
every `c > 0`, then for every `δ > 0` there are `C > 0` and `Y` such that
`W (x * u) / W x ≤ C * u ^ (ρ - δ)` for all `x ≥ Y` and `u ∈ (0, 1]`.
The proof chains the ratio limit at the dyadic scales `1/2` and `2`. -/
theorem potter_upper {W : ℝ → ℝ} {ρ : ℝ}
    (hW : Antitone W) (hWnn : ∀ t, 0 ≤ W t) (hWb : ∃ B, ∀ t, W t ≤ B)
    (hpos : ∀ᶠ x in atTop, 0 < W x)
    (hratio : ∀ c : ℝ, 0 < c → Tendsto (fun x => W (c * x) / W x) atTop (𝓝 (c ^ ρ)))
    (hρ : ρ < 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∃ Y : ℝ, 0 < C ∧ 0 < Y ∧ ∀ x ≥ Y, ∀ u ∈ Set.Ioc 0 1,
      W (x * u) / W x ≤ C * u ^ (ρ - δ) := by
  obtain ⟨B, hB⟩ := hWb
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, ∀ x ≥ Y₀, 0 < W x := eventually_atTop.mp hpos
  have h2ρ : (0:ℝ) < (2:ℝ) ^ ρ := Real.rpow_pos_of_pos (by norm_num) ρ
  have h2ρ' : (0:ℝ) < (2:ℝ) ^ (-ρ) := Real.rpow_pos_of_pos (by norm_num) (-ρ)
  -- dyadic step down: `W (y / 2) / W y ≤ 2 ^ (-ρ + δ)`
  set e1 := (2:ℝ) ^ (-ρ) * ((2:ℝ) ^ δ - 1) with he1def
  have he1 : 0 < e1 :=
    mul_pos h2ρ' (by
      have h := Real.one_lt_rpow (show (1:ℝ) < 2 by norm_num) hδ
      linarith)
  obtain ⟨Y₁, hY₁⟩ := (Metric.tendsto_atTop.mp (hratio (1 / 2) (by norm_num))) e1 he1
  -- dyadic step up: `2 ^ (ρ - δ / 2) ≤ W (2 * y) / W y`
  set e2 := (2:ℝ) ^ ρ - (2:ℝ) ^ (ρ - δ / 2) with he2def
  have he2 : 0 < e2 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1:ℝ) < 2 by norm_num)
      (show ρ - δ / 2 < ρ by linarith)
    linarith
  obtain ⟨Y₂, hY₂⟩ := (Metric.tendsto_atTop.mp (hratio 2 (by norm_num))) e2 he2
  set Y := max (max (max Y₀ Y₁) Y₂) 1 with hYdef
  have hYpos : 0 < Y := lt_max_iff.mpr (Or.inr one_pos)
  have hYle : Y₀ ≤ Y := by
    have h1 : Y₀ ≤ max Y₀ Y₁ := le_max_of_le_left le_rfl
    have h2 : max Y₀ Y₁ ≤ max (max Y₀ Y₁) Y₂ := le_max_of_le_left le_rfl
    have h3 : max (max Y₀ Y₁) Y₂ ≤ max (max (max Y₀ Y₁) Y₂) 1 := le_max_of_le_left le_rfl
    exact le_trans (le_trans h1 h2) h3
  have hY1le : Y₁ ≤ Y := by
    have h1 : Y₁ ≤ max Y₀ Y₁ := le_max_of_le_right le_rfl
    have h2 : max Y₀ Y₁ ≤ max (max Y₀ Y₁) Y₂ := le_max_of_le_left le_rfl
    have h3 : max (max Y₀ Y₁) Y₂ ≤ max (max (max Y₀ Y₁) Y₂) 1 := le_max_of_le_left le_rfl
    exact le_trans (le_trans h1 h2) h3
  have hY2le : Y₂ ≤ Y := by
    have h1 : Y₂ ≤ max (max Y₀ Y₁) Y₂ := le_max_of_le_right le_rfl
    have h2 : max (max Y₀ Y₁) Y₂ ≤ max (max (max Y₀ Y₁) Y₂) 1 := le_max_of_le_left le_rfl
    exact le_trans h1 h2
  have hWpos : ∀ t ≥ Y, 0 < W t := fun t ht => hY₀ t (le_trans hYle ht)
  have hWpos' : ∀ t ≥ Y, W t ≠ 0 := fun t ht => ne_of_gt (hWpos t ht)
  -- step bounds
  have hstep_half : ∀ y ≥ Y, W ((1 / 2) * y) / W y ≤ (2:ℝ) ^ (-ρ + δ) := by
    intro y hy
    have hy1 : y ≥ Y₁ := le_trans hY1le hy
    have h := hY₁ y hy1
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    have h12 : ((1:ℝ) / 2) ^ ρ = (2:ℝ) ^ (-ρ) := by
      rw [one_div, ← Real.rpow_neg_one (2:ℝ), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      simp
    have hle : W ((1 / 2) * y) / W y ≤ ((1:ℝ) / 2) ^ ρ + e1 := by linarith [h.2]
    rw [h12] at hle
    have hsplit : (2:ℝ) ^ (-ρ) + e1 = (2:ℝ) ^ (-ρ + δ) := by
      rw [he1def]
      have h1 : (2:ℝ) ^ (-ρ) + (2:ℝ) ^ (-ρ) * ((2:ℝ) ^ δ - 1)
          = (2:ℝ) ^ (-ρ) * (2:ℝ) ^ δ := by ring
      rw [h1, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    linarith
  have hstep_two : ∀ y ≥ Y, (2:ℝ) ^ (ρ - δ / 2) ≤ W (2 * y) / W y := by
    intro y hy
    have hy2 : y ≥ Y₂ := le_trans hY2le hy
    have h := hY₂ y hy2
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.1]
  -- lower bound: `W Y * 2 ^ (ρ - δ / 2) * (x / Y) ^ (ρ - δ / 2) ≤ W x`
  have hclaim : ∀ x ≥ Y,
      W Y * (2:ℝ) ^ (ρ - δ / 2) * (x / Y) ^ (ρ - δ / 2) ≤ W x := by
    intro x hx
    have hxY : (1:ℝ) ≤ x / Y := by
      rw [le_div_iff₀ hYpos]
      simpa using hx
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hxY (show (1:ℝ) < 2 by norm_num)
    set yk := (2:ℝ) ^ k * Y with hykdef
    have hykY : yk ≥ Y := by
      rw [hykdef]
      have h1 : (1:ℝ) ≤ (2:ℝ) ^ k := one_le_pow₀ (by norm_num)
      have h2 : (1:ℝ) * Y ≤ (2:ℝ) ^ k * Y := by exact mul_le_mul_of_nonneg_right h1 hYpos.le
      simpa using h2
    have hykpos : 0 < yk := lt_of_lt_of_le hYpos hykY
    have hykx : yk ≤ x := by
      rw [hykdef]
      exact (le_div_iff₀ hYpos).mp hk1
    -- chain product
    have hchain : ((2:ℝ) ^ (ρ - δ / 2)) ^ k ≤ W yk / W Y := by
      show ((2:ℝ) ^ (ρ - δ / 2)) ^ k ≤ W ((2:ℝ) ^ k * Y) / W Y
      have htel := prod_range_div_telescope (f := fun j => W ((2:ℝ) ^ j * Y))
        (n := k) (fun i _hi => hWpos' _ (by
          have h1 : (1:ℝ) ≤ (2:ℝ) ^ i := one_le_pow₀ (by norm_num)
          have h2 : (1:ℝ) * Y ≤ (2:ℝ) ^ i * Y :=
            mul_le_mul_of_nonneg_right h1 hYpos.le
          simpa using h2))
      simp only [pow_zero, one_mul] at htel
      rw [← htel]
      have hfactor : ∀ j ∈ Finset.range k,
          (2:ℝ) ^ (ρ - δ / 2) ≤ W ((2:ℝ) ^ (j + 1) * Y) / W ((2:ℝ) ^ j * Y) := by
        intro j _
        have harg : (2:ℝ) ^ j * Y ≥ Y := by
          have h1 : (1:ℝ) ≤ (2:ℝ) ^ j := one_le_pow₀ (by norm_num)
          have h2 : (1:ℝ) * Y ≤ (2:ℝ) ^ j * Y :=
            mul_le_mul_of_nonneg_right h1 hYpos.le
          simpa using h2
        have hstep := hstep_two ((2:ℝ) ^ j * Y) harg
        have heq : (2:ℝ) * ((2:ℝ) ^ j * Y) = (2:ℝ) ^ (j + 1) * Y := by
          rw [pow_succ]; ring
        rwa [heq] at hstep
      calc ((2:ℝ) ^ (ρ - δ / 2)) ^ k
          = ∏ _j ∈ Finset.range k, (2:ℝ) ^ (ρ - δ / 2) := by
            rw [Finset.prod_const, Finset.card_range]
        _ ≤ ∏ j ∈ Finset.range k,
            W ((2:ℝ) ^ (j + 1) * Y) / W ((2:ℝ) ^ j * Y) := by
            exact prod_le_prod_of_le (fun i _ => by positivity)
              (fun i hi => hfactor i (Finset.mem_range.mpr hi))
    -- partial step: `W x / W yk ≥ 2 ^ (ρ - δ / 2)`
    have hpart : (2:ℝ) ^ (ρ - δ / 2) ≤ W x / W yk := by
      have hlam : x / yk ≤ 2 := by
        rw [div_le_iff₀ hykpos]
        have h2 : x < (2:ℝ) ^ (k + 1) * Y := by
          have h := hk2
          rwa [div_lt_iff₀ hYpos] at h
        have h3 : (2:ℝ) ^ (k + 1) * Y = 2 * yk := by rw [hykdef, pow_succ]; ring
        rw [h3] at h2
        exact le_of_lt h2
      have hlamx : x / yk * yk = x := div_mul_cancel₀ x (ne_of_gt hykpos)
      have hstep := hstep_two yk hykY
      have hmono : W (2 * yk) ≤ W (x / yk * yk) :=
        hW (by
          have h1 : x / yk * yk ≤ 2 * yk := by
            exact mul_le_mul_of_nonneg_right hlam hykpos.le
          exact h1)
      rw [hlamx] at hmono
      have hWk : 0 < W yk := hWpos yk hykY
      rw [le_div_iff₀ hWk]
      calc (2:ℝ) ^ (ρ - δ / 2) * W yk ≤ (W (2 * yk) / W yk) * W yk := by
            exact mul_le_mul_of_nonneg_right hstep hWk.le
        _ = W (2 * yk) := div_mul_cancel₀ _ (ne_of_gt hWk)
        _ ≤ W x := hmono
    -- combine
    have hWk : 0 < W yk := hWpos yk hykY
    have hWY : 0 < W Y := hWpos Y le_rfl
    have h1 : W Y * ((2:ℝ) ^ (ρ - δ / 2)) ^ k ≤ W yk := by
      have h := (le_div_iff₀ hWY).mp hchain
      calc W Y * ((2:ℝ) ^ (ρ - δ / 2)) ^ k
          = ((2:ℝ) ^ (ρ - δ / 2)) ^ k * W Y := by ring
        _ ≤ W yk := h
    have h2 : W yk * (2:ℝ) ^ (ρ - δ / 2) ≤ W x := by
      have h := (le_div_iff₀ hWk).mp hpart
      calc W yk * (2:ℝ) ^ (ρ - δ / 2)
          = (2:ℝ) ^ (ρ - δ / 2) * W yk := by ring
        _ ≤ W x := h
    have h3 : W Y * ((2:ℝ) ^ (ρ - δ / 2)) ^ k * (2:ℝ) ^ (ρ - δ / 2) ≤ W x := by
      calc W Y * ((2:ℝ) ^ (ρ - δ / 2)) ^ k * (2:ℝ) ^ (ρ - δ / 2)
          = (W Y * ((2:ℝ) ^ (ρ - δ / 2)) ^ k) * (2:ℝ) ^ (ρ - δ / 2) := by ring
        _ ≤ W yk * (2:ℝ) ^ (ρ - δ / 2) := by
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ W x := h2
    have h4 : (x / Y) ^ (ρ - δ / 2) ≤ ((2:ℝ) ^ k) ^ (ρ - δ / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hk1 (by linarith)
    have h5 : ((2:ℝ) ^ (ρ - δ / 2)) ^ k * (2:ℝ) ^ (ρ - δ / 2)
        = (2:ℝ) ^ (ρ - δ / 2) * ((2:ℝ) ^ k) ^ (ρ - δ / 2) := by
      have h6 : ((2:ℝ) ^ (ρ - δ / 2)) ^ k = ((2:ℝ) ^ k) ^ (ρ - δ / 2) := by
        have h7 : ((2:ℝ) ^ (ρ - δ / 2)) ^ k = (2:ℝ) ^ ((ρ - δ / 2) * (k : ℝ)) := by
          rw [← Real.rpow_natCast ((2:ℝ) ^ (ρ - δ / 2)) k]
          exact (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
        have h8 : ((2:ℝ) ^ k) ^ (ρ - δ / 2) = (2:ℝ) ^ ((k : ℝ) * (ρ - δ / 2)) := by
          rw [← Real.rpow_natCast (2:ℝ) k]
          exact (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
        rw [h7, h8, mul_comm]
      rw [h6]; ring
    calc W Y * (2:ℝ) ^ (ρ - δ / 2) * (x / Y) ^ (ρ - δ / 2)
        ≤ W Y * (2:ℝ) ^ (ρ - δ / 2) * ((2:ℝ) ^ k) ^ (ρ - δ / 2) := by
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = W Y * (((2:ℝ) ^ (ρ - δ / 2)) ^ k * (2:ℝ) ^ (ρ - δ / 2)) := by
          rw [h5]; ring
      _ = W Y * ((2:ℝ) ^ (ρ - δ / 2)) ^ k * (2:ℝ) ^ (ρ - δ / 2) := by ring
      _ ≤ W x := h3
  -- final assembly
  set D := W Y * (2:ℝ) ^ (ρ - δ / 2) with hDdef
  have hD : 0 < D := mul_pos (hWpos Y le_rfl) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨max ((2:ℝ) ^ (-ρ + δ)) (B / D), Y, by positivity, hYpos, ?_⟩
  intro x hx u hu
  obtain ⟨hu0, hu1⟩ := hu
  have huinv : u ≤ 1 / u := by
    rw [le_div_iff₀ hu0]
    calc u * u ≤ 1 * 1 := mul_le_mul hu1 hu1 hu0.le zero_le_one
      _ = 1 := by norm_num
  have hxpos : 0 < x := lt_of_lt_of_le hYpos hx
  have hWx : 0 < W x := hWpos x hx
  by_cases hcase : Y ≤ x * u
  · -- Case A: `x * u ≥ Y`
    obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (show (1:ℝ) ≤ 1 / u by
      rw [le_div_iff₀ hu0]; simpa using hu1) (show (1:ℝ) < 2 by norm_num)
    set y := x / (2:ℝ) ^ m with hydef
    have hu2 : u * (2:ℝ) ^ m ≤ 1 := by
      have h1 : (2:ℝ) ^ m ≤ 1 / u := hm1
      rw [le_div_iff₀ hu0] at h1
      calc u * (2:ℝ) ^ m = (2:ℝ) ^ m * u := by ring
        _ ≤ 1 := h1
    have hyY : y ≥ Y := by
      rw [hydef]
      calc Y ≤ x * u := hcase
        _ ≤ x / (2:ℝ) ^ m := by
            rw [le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ) ^ m)]
            calc (x * u) * (2:ℝ) ^ m = x * (u * (2:ℝ) ^ m) := by ring
              _ ≤ x * 1 := mul_le_mul_of_nonneg_left hu2 hxpos.le
              _ = x := mul_one x
    -- `W (x * u) ≤ W (y / 2) * ...`
    have hxu : x * u ≤ y := by
      rw [hydef, le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ) ^ m)]
      calc x * u * (2:ℝ) ^ m = x * (u * (2:ℝ) ^ m) := by ring
        _ ≤ x * 1 := mul_le_mul_of_nonneg_left hu2 hxpos.le
        _ = x := mul_one x
    have hxu2 : y / 2 < x * u := by
      rw [hydef]
      have h1 : (2:ℝ) ^ (-(m : ℝ)) < 2 * u := by
        have h2 : 1 / u < (2:ℝ) ^ (m + 1) := hm2
        rw [div_lt_iff₀ hu0] at h2
        have h3 : (2:ℝ) ^ (-(m : ℝ)) = 1 / (2:ℝ) ^ m := by
          rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
          exact inv_eq_one_div _
        rw [h3, div_lt_iff₀ (by positivity : (0:ℝ) < (2:ℝ) ^ m)]
        calc (1:ℝ) < (2:ℝ) ^ (m + 1) * u := by linarith [h2]
          _ = 2 * u * (2:ℝ) ^ m := by rw [pow_succ]; ring
      have h2 : x / (2:ℝ) ^ m / 2 = x * ((2:ℝ) ^ (-(m : ℝ)) / 2) := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
        field_simp
      rw [h2]
      have h3 : x * ((2:ℝ) ^ (-(m : ℝ)) / 2) < x * u := by
        apply mul_lt_mul_of_pos_left _ hxpos
        linarith [h1]
      exact h3
    have hWxu : W (x * u) ≤ W (y / 2) := hW (le_of_lt hxu2)
    have hstep1 : W (y / 2) / W y ≤ (2:ℝ) ^ (-ρ + δ) := by
      have h := hstep_half y hyY
      have heq : (1 / 2) * y = y / 2 := by ring
      rwa [heq] at h
    have hWy : 0 < W y := hWpos y hyY
    have hum2 : (1:ℝ) < (2:ℝ) ^ (m + 1) * u := by
      have h2 : 1 / u < (2:ℝ) ^ (m + 1) := hm2
      rw [div_lt_iff₀ hu0] at h2
      linarith [h2]
    have harg : ∀ j ≤ m, x / (2:ℝ) ^ j ≥ Y := by
      intro j hj
      have h2 : (2:ℝ) ^ j ≤ (2:ℝ) ^ m :=
        pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj
      have h3 : x / (2:ℝ) ^ m ≤ x / (2:ℝ) ^ j := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        exact mul_le_mul_of_nonneg_left h2 hxpos.le
      exact le_trans hyY h3
    have hchain : W y / W x ≤ ((2:ℝ) ^ (-ρ + δ)) ^ m := by
      show W (x / (2:ℝ) ^ m) / W x ≤ _
      have htel := prod_range_div_telescope (f := fun j => W (x / (2:ℝ) ^ j))
        (n := m) (fun i _hi => hWpos' _ (le_trans hyY (by
          have h2 : (2:ℝ) ^ i ≤ (2:ℝ) ^ m :=
            pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) _hi
          rw [hydef]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          exact mul_le_mul_of_nonneg_left h2 hxpos.le)))
      simp only [pow_zero, div_one] at htel
      rw [← htel]
      have hfactor : ∀ j ∈ Finset.range m,
          W (x / (2:ℝ) ^ (j + 1)) / W (x / (2:ℝ) ^ j) ≤ (2:ℝ) ^ (-ρ + δ) := by
        intro j _
        have hargj : x / (2:ℝ) ^ j ≥ Y :=
          harg j (Finset.mem_range.mp ‹j ∈ Finset.range m›).le
        have hstep := hstep_half (x / (2:ℝ) ^ j) hargj
        have heq : (1 / 2) * (x / (2:ℝ) ^ j) = x / (2:ℝ) ^ (j + 1) := by
          rw [pow_succ]; field_simp
        rwa [heq] at hstep
      calc ∏ j ∈ Finset.range m,
            W (x / (2:ℝ) ^ (j + 1)) / W (x / (2:ℝ) ^ j)
          ≤ ∏ _j ∈ Finset.range m, (2:ℝ) ^ (-ρ + δ) := by
            apply prod_le_prod_of_le
            · intro i hi
              exact div_nonneg (hWnn _)
                (le_of_lt (hWpos _ (harg i hi.le)))
            · intro i hi
              exact hfactor i (Finset.mem_range.mpr hi)
        _ = ((2:ℝ) ^ (-ρ + δ)) ^ m := by
            rw [Finset.prod_const, Finset.card_range]
    have hA1 : W (x * u) / W x ≤ ((2:ℝ) ^ (-ρ + δ)) ^ (m + 1) := by
      have h1 : W (x * u) ≤ W y * (2:ℝ) ^ (-ρ + δ) := by
        have hle : W (x * u) / W y ≤ (2:ℝ) ^ (-ρ + δ) := by
          calc W (x * u) / W y ≤ W (y / 2) / W y :=
                div_le_div_of_nonneg_right hWxu hWy.le
            _ ≤ (2:ℝ) ^ (-ρ + δ) := hstep1
        have h2 := (div_le_iff₀ hWy).mp hle
        calc W (x * u) ≤ (2:ℝ) ^ (-ρ + δ) * W y := h2
          _ = W y * (2:ℝ) ^ (-ρ + δ) := by ring
      rw [div_le_iff₀ hWx]
      calc W (x * u) ≤ W y * (2:ℝ) ^ (-ρ + δ) := h1
        _ ≤ (W x * ((2:ℝ) ^ (-ρ + δ)) ^ m) * (2:ℝ) ^ (-ρ + δ) := by
            have h2 : W y ≤ W x * ((2:ℝ) ^ (-ρ + δ)) ^ m := by
              have h3 := hchain
              rw [div_le_iff₀ hWx] at h3
              calc W y ≤ ((2:ℝ) ^ (-ρ + δ)) ^ m * W x := h3
                _ = W x * ((2:ℝ) ^ (-ρ + δ)) ^ m := by ring
            exact mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = ((2:ℝ) ^ (-ρ + δ)) ^ (m + 1) * W x := by rw [pow_succ]; ring
    have hA2 : ((2:ℝ) ^ (-ρ + δ)) ^ (m + 1) ≤ (2:ℝ) ^ (-ρ + δ) * u ^ (ρ - δ) := by
      rw [pow_succ]
      have hkey : ((2:ℝ) ^ (-ρ + δ)) ^ m = ((2:ℝ) ^ (-(m : ℝ))) ^ (ρ - δ) := by
        have h7 : ((2:ℝ) ^ (-ρ + δ)) ^ m = (2:ℝ) ^ ((-ρ + δ) * (m : ℝ)) := by
          rw [← Real.rpow_natCast ((2:ℝ) ^ (-ρ + δ)) m]
          exact (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
        have h8 : ((2:ℝ) ^ (-(m : ℝ))) ^ (ρ - δ) = (2:ℝ) ^ ((-(m : ℝ)) * (ρ - δ)) := by
          exact (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
        rw [h7, h8]
        congr 1
        ring
      rw [hkey]
      have hle : ((2:ℝ) ^ (-(m : ℝ))) ^ (ρ - δ) ≤ u ^ (ρ - δ) := by
        apply Real.rpow_le_rpow_of_nonpos hu0 _ (by linarith)
        have h1 : u ≤ 1 / (2:ℝ) ^ m := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ) ^ m)]
          exact hu2
        have h3 : (2:ℝ) ^ (-(m : ℝ)) = 1 / (2:ℝ) ^ m := by
          rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
          exact inv_eq_one_div _
        rwa [h3]
      calc ((2:ℝ) ^ (-(m : ℝ))) ^ (ρ - δ) * (2:ℝ) ^ (-ρ + δ)
          ≤ u ^ (ρ - δ) * (2:ℝ) ^ (-ρ + δ) :=
            mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
        _ = (2:ℝ) ^ (-ρ + δ) * u ^ (ρ - δ) := by ring
    calc W (x * u) / W x ≤ ((2:ℝ) ^ (-ρ + δ)) ^ (m + 1) := hA1
      _ ≤ (2:ℝ) ^ (-ρ + δ) * u ^ (ρ - δ) := hA2
      _ ≤ max ((2:ℝ) ^ (-ρ + δ)) (B / D) * u ^ (ρ - δ) := by
          exact mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg hu0.le _)
  · -- Case B: `x * u < Y`
    have hcase : x * u < Y := lt_of_not_ge hcase
    have hclaimx := hclaim x hx
    have hxY1 : (1:ℝ) ≤ x / Y := by
      rw [le_div_iff₀ hYpos]
      simpa using hx
    have hB0 : 0 ≤ B := le_trans (hWnn 0) (hB 0)
    have hbound : W (x * u) / W x ≤ (B / D) * u ^ (ρ - δ) := by
      have hD' : D * (x / Y) ^ (ρ - δ / 2) ≤ W x := by
        calc D * (x / Y) ^ (ρ - δ / 2)
            = W Y * (2:ℝ) ^ (ρ - δ / 2) * (x / Y) ^ (ρ - δ / 2) := by
              rw [hDdef]
          _ ≤ W x := hclaimx
      have hpos1 : 0 < D * (x / Y) ^ (ρ - δ / 2) :=
        mul_pos hD (Real.rpow_pos_of_pos (by positivity) _)
      have h1 : W (x * u) / W x ≤ B / (D * (x / Y) ^ (ρ - δ / 2)) := by
        rw [div_le_iff₀ hWx, div_mul_eq_mul_div, le_div_iff₀ hpos1]
        exact mul_le_mul (hB _) hD' hpos1.le (le_trans (hWnn 0) (hB 0))
      calc W (x * u) / W x ≤ B / (D * (x / Y) ^ (ρ - δ / 2)) := h1
        _ = (B / D) * (x / Y) ^ (-(ρ - δ / 2)) := by
            rw [div_mul_eq_div_div, div_eq_mul_inv,
              ← Real.rpow_neg (by positivity : (0:ℝ) ≤ x / Y)]
        _ ≤ (B / D) * (x / Y) ^ (-ρ + δ) := by
            apply mul_le_mul_of_nonneg_left _ (div_nonneg hB0 hD.le)
            apply Real.rpow_le_rpow_of_exponent_le hxY1
            linarith
        _ ≤ (B / D) * u ^ (ρ - δ) := by
            apply mul_le_mul_of_nonneg_left _ (div_nonneg hB0 hD.le)
            have hYX : (0:ℝ) < Y / x := div_pos hYpos hxpos
            have hu' : u < Y / x := by
              rw [lt_div_iff₀ hxpos]
              calc u * x = x * u := by ring
                _ < Y := hcase
            have h1 := Real.rpow_lt_rpow_of_neg hu0 hu' (show ρ - δ < 0 by linarith)
            have h2 : (Y / x) ^ (ρ - δ) = (x / Y) ^ (-ρ + δ) := by
              have h3 : Y / x = (x / Y)⁻¹ := by field_simp
              rw [h3, Real.inv_rpow (by positivity : (0:ℝ) ≤ x / Y),
                ← Real.rpow_neg (by positivity : (0:ℝ) ≤ x / Y)]
              congr 1
              ring
            rw [h2] at h1
            exact le_of_lt h1
    calc W (x * u) / W x ≤ (B / D) * u ^ (ρ - δ) := hbound
      _ ≤ max ((2:ℝ) ^ (-ρ + δ)) (B / D) * u ^ (ρ - δ) := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.rpow_nonneg hu0.le _)

/-- **Karamata's integral theorem** for antitone functions with a ratio limit.
If `W` is antitone, nonnegative, bounded, eventually positive and
`W (c * x) / W x → c ^ ρ` for every `c > 0`, then for `β ≥ 0` and
`β + 1 + ρ > 0`,
`(∫ t in (0)..x, t ^ β * W t) / (x ^ (β + 1) * W x) → 1 / (β + 1 + ρ)`.
The proof substitutes `t = x * u` and applies dominated convergence with
Potter's bound as the dominator. -/
theorem karamata_integral {W : ℝ → ℝ} {ρ β : ℝ}
    (hW : Antitone W) (hWnn : ∀ t, 0 ≤ W t) (hWb : ∃ B, ∀ t, W t ≤ B)
    (hpos : ∀ᶠ x in atTop, 0 < W x)
    (hratio : ∀ c : ℝ, 0 < c → Tendsto (fun x => W (c * x) / W x) atTop (𝓝 (c ^ ρ)))
    (hρ : ρ < 0) (hβ : 0 ≤ β) (hβρ : 0 < β + 1 + ρ) :
    Tendsto (fun x => (∫ t in (0:ℝ)..x, t ^ β * W t) / (x ^ (β + 1) * W x))
      atTop (𝓝 (1 / (β + 1 + ρ))) := by
  -- Potter's bound with slack `δ = (β + 1 + ρ) / 2`
  obtain ⟨C, Y, hC, hYpos, hPotter⟩ :=
    potter_upper hW hWnn hWb hpos hratio hρ (δ := (β + 1 + ρ) / 2) (by linarith)
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, ∀ x ≥ Y₀, 0 < W x := eventually_atTop.mp hpos
  set Y' := max Y Y₀ with hY'def
  have hY'pos : 0 < Y' := lt_of_lt_of_le hYpos (le_max_left _ _)
  have hWpos : ∀ x ≥ Y', 0 < W x := fun x hx =>
    hY₀ x (le_trans (le_max_right _ _) hx)
  have hPotter' : ∀ x ≥ Y', ∀ u ∈ Set.Ioc 0 1,
      W (x * u) / W x ≤ C * u ^ (ρ - (β + 1 + ρ) / 2) :=
    fun x hx u hu => hPotter x (le_trans (le_max_left _ _) hx) u hu
  -- the ratio at `x ≥ Y'` equals the integral of the rescaled integrand
  have hEq : ∀ᶠ x in atTop,
      (∫ t in (0:ℝ)..x, t ^ β * W t) / (x ^ (β + 1) * W x)
        = ∫ u in (0:ℝ)..1, u ^ β * (W (x * u) / W x) := by
    filter_upwards [eventually_ge_atTop Y'] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le hY'pos hx
    have hWx : 0 < W x := hWpos x hx
    have h3 : (∫ u in (0:ℝ)..1, u ^ β * (W (x * u) / W x))
        = (∫ u in (0:ℝ)..1, u ^ β * W (x * u)) / W x := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro u _
      show u ^ β * (W (x * u) / W x) = (u ^ β * W (x * u)) / W x
      rw [mul_div_assoc]
    have hsub : ∫ t in (0:ℝ)..x, t ^ β * W t
        = x ^ (β + 1) * ∫ u in (0:ℝ)..1, u ^ β * W (x * u) := by
      have h1 : ∫ t in (0:ℝ)..x, t ^ β * W t
          = x * ∫ u in (0:ℝ)..1, (x * u) ^ β * W (x * u) := by
        have h0 : ∫ u in (0:ℝ)..1, (x * u) ^ β * W (x * u)
            = x⁻¹ * ∫ t in (0:ℝ)..x, t ^ β * W t := by
          have h0' := intervalIntegral.integral_comp_mul_left (fun t => t ^ β * W t)
            (a := (0:ℝ)) (b := (1:ℝ)) hxpos.ne'
          rw [smul_eq_mul] at h0'
          simpa using h0'
        rw [h0, ← mul_assoc, mul_inv_cancel₀ hxpos.ne', one_mul]
      have h2 : ∫ u in (0:ℝ)..1, (x * u) ^ β * W (x * u)
          = x ^ β * ∫ u in (0:ℝ)..1, u ^ β * W (x * u) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro u hu
        have huIcc : u ∈ Set.Icc (0:ℝ) 1 := by
          simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hu
        show (x * u) ^ β * W (x * u) = x ^ β * (u ^ β * W (x * u))
        rw [Real.mul_rpow hxpos.le (Set.mem_Icc.mp huIcc).1]
        ring
      rw [h1, h2]
      have hxβ1 : x * x ^ β = x ^ (β + 1) := by
        have h := Real.rpow_add hxpos (1 : ℝ) β
        rw [Real.rpow_one] at h
        rw [← h]
        congr 1
        ring
      calc x * (x ^ β * ∫ u in (0:ℝ)..1, u ^ β * W (x * u))
          = (x * x ^ β) * ∫ u in (0:ℝ)..1, u ^ β * W (x * u) := by ring
        _ = x ^ (β + 1) * ∫ u in (0:ℝ)..1, u ^ β * W (x * u) := by rw [hxβ1]
    rw [hsub]
    have hxp : x ^ (β + 1) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hxpos _)
    rw [mul_div_mul_left _ _ hxp]
    exact h3.symm
  -- dominated convergence for the rescaled integrand
  set δ' := (β + 1 + ρ) / 2 with hδ'def
  have hδ'pos : 0 < δ' := by linarith
  have hDCT : Tendsto (fun x => ∫ u in (0:ℝ)..1, u ^ β * (W (x * u) / W x))
      atTop (𝓝 (∫ u in (0:ℝ)..1, u ^ (β + ρ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun u => C * u ^ (β + ρ - δ'))
    · -- measurability of the rescaled integrand
      filter_upwards [eventually_ge_atTop Y'] with x hx
      have hxpos : 0 < x := lt_of_lt_of_le hY'pos hx
      have hmeas : Measurable (fun u => u ^ β * (W (x * u) / W x)) :=
        (Real.continuous_rpow_const hβ).measurable.mul
          (((hW.measurable).comp (measurable_const_mul x)).div_const _)
      exact (hmeas.aestronglyMeasurable).restrict
    · -- domination by Potter's bound
      filter_upwards [eventually_ge_atTop Y'] with x hx
      apply Filter.Eventually.of_forall
      intro u hu
      have huIoc : u ∈ Set.Ioc (0:ℝ) 1 := by
        simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hu
      have hu0 : 0 < u := huIoc.1
      have hWx : 0 < W x := hWpos x hx
      have hnn : 0 ≤ u ^ β * (W (x * u) / W x) :=
        mul_nonneg (Real.rpow_nonneg hu0.le _)
          (div_nonneg (hWnn _) hWx.le)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      calc u ^ β * (W (x * u) / W x)
          ≤ u ^ β * (C * u ^ (ρ - δ')) :=
            mul_le_mul_of_nonneg_left (hPotter' x hx u huIoc)
              (Real.rpow_nonneg hu0.le _)
        _ = C * u ^ (β + ρ - δ') := by
            have h := Real.rpow_add hu0 β (ρ - δ')
            calc u ^ β * (C * u ^ (ρ - δ'))
                = C * (u ^ β * u ^ (ρ - δ')) := by ring
              _ = C * u ^ (β + (ρ - δ')) := by rw [h]
              _ = C * u ^ (β + ρ - δ') := by congr 2; ring
    · -- integrability of the dominator
      apply IntervalIntegrable.const_mul
      apply intervalIntegral.intervalIntegrable_rpow'
      linarith
    · -- pointwise convergence
      apply Filter.Eventually.of_forall
      intro u hu
      have huIoc : u ∈ Set.Ioc (0:ℝ) 1 := by
        simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hu
      have hu0 : 0 < u := huIoc.1
      have hlim : Tendsto (fun x => W (x * u) / W x) atTop (𝓝 (u ^ ρ)) :=
        (hratio u hu0).congr (fun x => by rw [mul_comm])
      have h := hlim.const_mul (u ^ β)
      rw [← Real.rpow_add hu0] at h
      exact h
  -- evaluate the limit integral
  have hInt : (∫ u in (0:ℝ)..1, u ^ (β + ρ)) = 1 / (β + 1 + ρ) := by
    rw [integral_rpow (Or.inl (by linarith : (-1:ℝ) < β + ρ))]
    rw [Real.one_rpow, Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < β + ρ + 1))]
    rw [sub_zero]
    congr 1
    ring
  rw [hInt] at hDCT
  have hEq' : (fun x => ∫ u in (0:ℝ)..1, u ^ β * (W (x * u) / W x)) =ᶠ[atTop]
      (fun x => (∫ t in (0:ℝ)..x, t ^ β * W t) / (x ^ (β + 1) * W x)) :=
    Filter.EventuallyEq.symm hEq
  exact Filter.Tendsto.congr' hEq' hDCT

end MathlibExt.Probability.RegularVariation
