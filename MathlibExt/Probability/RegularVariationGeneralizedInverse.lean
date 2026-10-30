/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Order.Filter.AtTopBot.Basic
public import MathlibExt.Probability.RegularVariation

@[expose] public section

section

open Filter
open scoped Topology

namespace MathlibExt.Probability.RegularVariation

/-!
# Generalized inverse of a regularly varying function

For a regularly varying function `f` of index `-α` with `α > 0` that is
eventually non-increasing, there exists a sequence `a : ℕ → ℝ` of positive
reals (a "generalized inverse") such that `n · f (a n) → 1` as `n → ∞`.
This is a standard tool in the analysis of domains of attraction for stable
laws: it produces the normalizing constants from the tail function.

## Source

This formalizes `regularlyVarying_generalized_inverse` from
`v1/Atlas/TheoryOfProbability/code/RegularVariation.lean`, where it is left
unproved. The other two asymptotics in that file
(`regularlyVarying_truncated_moment`, `regularlyVarying_tail_integral`) are
not claimed here.

## Relation to Mathlib and to earlier batches

The predicates are the canonical `IsSlowlyVarying` and `IsRegularlyVarying`
from `MathlibExt.Probability.RegularVariation`. Slow variation uses eventual
positivity. The proof chooses a threshold above the positivity, representation,
and monotonicity thresholds before evaluating the slowly varying factor.

## Main results

* `regularlyVarying_generalized_inverse`: the generalized-inverse sequence.

## Proof outline

Write `f x = x ^ (-α) * L x` eventually, with `L` slowly varying. First,
`f → 0` at infinity: along the dyadic sequence `u k = f (2 ^ k * X0)` the
ratio `u (k + 1) / u k → 2 ^ (-α) < 1`, while `u` is antitone and bounded
below by `0`, so its limit `L*` satisfies `L* = 2 ^ (-α) * L*`, hence
`L* = 0`, and monotonicity spreads this to all of `f`. Let
`a n = max 1 (sSup {x | (n : ℝ)⁻¹ ≤ f x})`. Since `f → 0`, each level set
is bounded above; since `f` is eventually positive, `a n → ∞`, and
eventually `a n` is the supremum. The supremum property gives, for every
`δ > 0`, `f ((1 + δ) * a n) ≤ 1 / n`, and for every `δ ∈ (0, 1 / 2]`,
`f ((1 - δ) * a n) ≥ 1 / n` (an upper bound for the level set). Regular
variation gives the ratios `f ((1 ± δ) * a n) / f (a n) → (1 ± δ) ^ (-α)`,
so `n * f (a n)` is eventually squeezed between `(1 - δ) ^ α` and
`(1 + δ) ^ α`; letting `δ → 0` gives the limit `1`.
-/

/-- Ratio form of regular variation: `f (c * x) / f x → c ^ ρ` as
`x → ∞`, for every `c > 0`. -/
private theorem tendsto_ratio {f : ℝ → ℝ} {ρ : ℝ} {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L)
    (hrep : ∀ᶠ x in atTop, f x = x ^ ρ * L x) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ ρ)) := by
  have hpos : ∀ᶠ x in atTop, 0 < f x := by
    filter_upwards [hrep, hL.1, eventually_gt_atTop (0 : ℝ)] with x hx hLx hx0
    rw [hx]
    exact mul_pos (Real.rpow_pos_of_pos hx0 ρ) hLx
  have hcx : ∀ᶠ x in atTop, f (c * x) = (c * x) ^ ρ * L (c * x) :=
    (tendsto_id.const_mul_atTop hc).eventually hrep
  have hev : ∀ᶠ x in atTop, f (c * x) / f x = c ^ ρ * (L (c * x) / L x) := by
    filter_upwards [hrep, hL.1, eventually_gt_atTop (0 : ℝ), hpos, hcx] with x hx hLx hx0 hfx hcx'
    rw [hcx', hx, Real.mul_rpow hc.le hx0.le]
    have h1 : (x : ℝ) ^ ρ ≠ 0 := (Real.rpow_pos_of_pos hx0 ρ).ne'
    have h2 : L x ≠ 0 := hLx.ne'
    field_simp
  have hmul : Tendsto (fun x => c ^ ρ * (L (c * x) / L x)) atTop (𝓝 (c ^ ρ)) := by
    have h := (hL.2 c hc).const_mul (c ^ ρ)
    simpa using h
  exact Tendsto.congr' (Filter.EventuallyEq.symm hev) hmul

/-- A regularly varying function of negative index that is eventually
non-increasing tends to `0` at infinity. -/
private theorem tendsto_zero_of_antitone_regVarying {f : ℝ → ℝ} {α : ℝ}
    (hα : 0 < α) {L : ℝ → ℝ} (hL : IsSlowlyVarying L) {X0 : ℝ} (hX0 : 0 < X0)
    (hmono : ∀ x, X0 ≤ x → ∀ y, x ≤ y → f y ≤ f x)
    (hrep : ∀ x, X0 ≤ x → f x = x ^ (-α) * L x)
    (hLpos : ∀ x, X0 ≤ x → 0 < L x) :
    Tendsto f atTop (𝓝 0) := by
  set u : ℕ → ℝ := fun k => f ((2 : ℝ) ^ k * X0) with hu
  have h2k : ∀ k : ℕ, X0 ≤ (2 : ℝ) ^ k * X0 := fun k => by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    calc X0 = 1 * X0 := (one_mul _).symm
      _ ≤ (2 : ℝ) ^ k * X0 :=
        mul_le_mul_of_nonneg_right h1 hX0.le
  have hanti : Antitone u := by
    intro a b hab
    simp only [hu]
    apply hmono _ (h2k a) _ _
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hab) hX0.le
  have hpos_u : ∀ k, 0 < u k := fun k => by
    simp only [hu]
    rw [hrep _ (h2k k)]
    exact mul_pos (Real.rpow_pos_of_pos (mul_pos (pow_pos (by norm_num) k) hX0) _)
      (hLpos _ (h2k k))
  have hbddBelow : BddBelow (Set.range u) :=
    ⟨0, fun y ⟨k, hk⟩ => hk ▸ (hpos_u k).le⟩
  have hlim := tendsto_atTop_ciInf hanti hbddBelow
  have hxk : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * X0) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have h2 := h1.const_mul_atTop hX0
    exact h2.congr (fun k => by ring)
  have hratio : Tendsto (fun k : ℕ => u (k + 1) / u k) atTop (𝓝 ((2 : ℝ) ^ (-α))) := by
    have hmain := (tendsto_ratio hL (eventually_atTop.mpr ⟨X0, fun x hx => hrep x hx⟩)
      (c := 2) (by norm_num)).comp hxk
    refine hmain.congr (fun k => ?_)
    simp only [hu, Function.comp_apply]
    congr 1
    · congr 1
      rw [pow_succ']
      ring
  have hshift : Tendsto (fun k : ℕ => u (k + 1)) atTop (𝓝 (⨅ i, u i)) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hprod : Tendsto (fun k : ℕ => (u (k + 1) / u k) * u k) atTop
      (𝓝 ((2 : ℝ) ^ (-α) * (⨅ i, u i))) := hratio.mul hlim
  have heq : (⨅ i, u i) = (2 : ℝ) ^ (-α) * (⨅ i, u i) := by
    have h1 : Tendsto (fun k : ℕ => (u (k + 1) / u k) * u k) atTop (𝓝 (⨅ i, u i)) := by
      refine hshift.congr (fun k => ?_)
      rw [div_mul_cancel₀ _ (hpos_u k).ne']
    exact tendsto_nhds_unique h1 hprod
  have hne : (2 : ℝ) ^ (-α) ≠ 1 := by
    have hlt : (2 : ℝ) ^ (-α) < 1 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hα)
    exact ne_of_lt hlt
  have hLzero : (⨅ i, u i) = 0 := by
    have hmul : (⨅ i, u i) * (1 - (2 : ℝ) ^ (-α)) = 0 := by
      rw [show (⨅ i, u i) * (1 - (2 : ℝ) ^ (-α))
          = (⨅ i, u i) - (2 : ℝ) ^ (-α) * (⨅ i, u i) by ring, ← heq, sub_self]
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hne
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hu0 : Tendsto u atTop (𝓝 0) := by rwa [hLzero] at hlim
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hu0) ε hε
  refine ⟨(2 : ℝ) ^ K * X0, fun x hx => ?_⟩
  have hfx : f x ≤ u K := by
    simp only [hu]
    exact hmono _ (h2k K) x hx
  have hK' : dist (u K) 0 < ε := hK K le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_pos (hpos_u K)] at hK'
  have hfxpos : 0 < f x := by
    rw [hrep x (le_trans (h2k K) hx)]
    exact mul_pos (Real.rpow_pos_of_pos
      (lt_of_lt_of_le (mul_pos (pow_pos (by norm_num) K) hX0) hx) _)
      (hLpos x (le_trans (h2k K) hx))
  rw [Real.dist_eq, sub_zero, abs_of_pos hfxpos]
  linarith [hK', hfx]

/-- **Generalized inverse of a regularly varying function.** For a regularly
varying function `f` of index `-α` with `α > 0` that is eventually
non-increasing, there exists a sequence `a : ℕ → ℝ` of positive reals such
that `n · f (a n) → 1` as `n → ∞`. -/
theorem regularlyVarying_generalized_inverse (f : ℝ → ℝ) (α : ℝ)
    (hα : 0 < α)
    (hf : IsRegularlyVarying f (-α))
    (hdecr : ∀ᶠ x in atTop, ∀ y, x ≤ y → f y ≤ f x) :
    ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧
      Tendsto (fun n => ↑n * f (a n)) atTop (𝓝 1) := by
  obtain ⟨L, hL, hrep⟩ := hf
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp hdecr
  obtain ⟨X2, hX2⟩ := eventually_atTop.mp hrep
  obtain ⟨X3, hX3⟩ := eventually_atTop.mp hL.1
  set X0 : ℝ := max (max (max X1 X2) X3) 1 with hX0def
  have hX0 : 0 < X0 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hX1le : X1 ≤ X0 :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hX2le : X2 ≤ X0 :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hX3le : X3 ≤ X0 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hLposX : ∀ x, X0 ≤ x → 0 < L x :=
    fun x hx => hX3 x (le_trans hX3le hx)
  have hmono : ∀ x, X0 ≤ x → ∀ y, x ≤ y → f y ≤ f x :=
    fun x hx y hy => hX1 x (le_trans hX1le hx) y hy
  have hrepX : ∀ x, X0 ≤ x → f x = x ^ (-α) * L x :=
    fun x hx => hX2 x (le_trans hX2le hx)
  have hposX : ∀ x, X0 ≤ x → 0 < f x := by
    intro x hx
    rw [hrepX x hx]
    exact mul_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le hX0 hx) _)
      (hLposX x hx)
  have hzero : Tendsto f atTop (𝓝 0) :=
    tendsto_zero_of_antitone_regVarying hα hL hX0 hmono hrepX hLposX
  classical
  set S : ℕ → Set ℝ := fun n => {x | (n : ℝ)⁻¹ ≤ f x} with hS
  have hBdd : ∀ n : ℕ, 1 ≤ n → BddAbove (S n) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
    obtain ⟨Y, hY⟩ := (Metric.tendsto_atTop.mp hzero) ((n : ℝ)⁻¹) (by positivity)
    refine ⟨max Y X0, mem_upperBounds.mpr fun x hx => ?_⟩
    by_contra hlt
    push Not at hlt
    have hxge : X0 ≤ x := le_trans (le_max_right _ _) (le_of_lt hlt)
    have hYle : Y ≤ x := le_trans (le_max_left _ _) (le_of_lt hlt)
    have hfx : f x ≤ f (max Y X0) := hmono _ (le_max_right _ _) x (le_of_lt hlt)
    have hsmall : f (max Y X0) < (n : ℝ)⁻¹ := by
      have h := hY (max Y X0) (le_max_left _ _)
      rw [Real.dist_eq, sub_zero, abs_of_pos (hposX _ (le_max_right _ _))] at h
      exact h
    have hx' : (↑n : ℝ)⁻¹ ≤ f x := hx
    linarith
  set a : ℕ → ℝ := fun n => max 1 (sSup (S n)) with ha
  have ha_pos : ∀ n, 0 < a n := fun n => lt_of_lt_of_le one_pos (le_max_left _ _)
  have ha_top : Tendsto a atTop atTop := by
    rw [tendsto_atTop]
    intro M
    set x := max M X0 + 1 with hxdef
    have hfx : 0 < f x := hposX x (by linarith [le_max_right M X0])
    obtain ⟨N, hN⟩ := exists_nat_gt ((f x)⁻¹)
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have hNpos : 0 < N := by
      have h : (0 : ℝ) < (N : ℝ) := lt_trans (inv_pos.mpr hfx) hN
      exact_mod_cast h
    have hn1 : 1 ≤ n := le_trans hNpos hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast lt_of_lt_of_le hNpos hn
    have h1 : (n : ℝ)⁻¹ ≤ f x := by
      rw [inv_le_iff_one_le_mul₀ hnpos]
      have hlt : (f x)⁻¹ < (n : ℝ) := by
        exact lt_of_lt_of_le hN (by exact_mod_cast hn)
      have hmul : (1 : ℝ) < (n : ℝ) * f x := by
        calc (1 : ℝ) = (f x)⁻¹ * f x := (inv_mul_cancel₀ hfx.ne').symm
          _ < (n : ℝ) * f x := by gcongr
      linarith
    have hxS : x ∈ S n := h1
    have hle : x ≤ sSup (S n) := le_csSup (hBdd n hn1) hxS
    calc M ≤ x := by linarith [le_max_left M X0]
      _ ≤ sSup (S n) := hle
      _ ≤ a n := le_max_right _ _
  have hev : ∀ᶠ n in atTop, 2 * X0 ≤ sSup (S n) ∧ a n = sSup (S n) ∧
      (S n).Nonempty ∧ BddAbove (S n) := by
    filter_upwards [ha_top.eventually (eventually_gt_atTop (max 1 (2 * X0 + 1))),
      eventually_ge_atTop 1] with n hn hn1
    have hbdd := hBdd n hn1
    have hs1 : (1 : ℝ) ≤ sSup (S n) := by
      by_contra hlt
      push Not at hlt
      have ha1 : a n = 1 := by simp only [ha, max_eq_left hlt.le]
      have hgt : (1 : ℝ) < a n := lt_trans (lt_max_iff.mpr (Or.inr (by linarith [hX0]))) hn
      rw [ha1] at hgt
      exact lt_irrefl _ hgt
    have ha_eq : a n = sSup (S n) := by simp only [ha, max_eq_right hs1]
    have h2X0 : 2 * X0 ≤ sSup (S n) := by
      have hle : 2 * X0 + 1 ≤ a n := le_trans (le_max_right _ _) hn.le
      rw [ha_eq] at hle
      linarith
    have hne : (S n).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, Real.sSup_empty] at hs1
      exact absurd hs1 (by norm_num)
    exact ⟨h2X0, ha_eq, hne, hbdd⟩
  have hC1 : ∀ᶠ (n : ℕ) in atTop, ∀ δ : ℝ, 0 < δ → f ((1 + δ) * a n) ≤ (↑n : ℝ)⁻¹ := by
    filter_upwards [hev] with n ⟨h2X0, ha_eq, hne, hbdd⟩ δ hδ
    by_contra hgt
    push Not at hgt
    have hmem : (1 + δ) * a n ∈ S n := hgt.le
    have hle : (1 + δ) * a n ≤ sSup (S n) := le_csSup hbdd hmem
    rw [← ha_eq] at hle
    have hapos : 0 < a n := ha_pos n
    nlinarith [hle, hapos, hδ]
  have hC2 : ∀ᶠ (n : ℕ) in atTop, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      (↑n : ℝ)⁻¹ ≤ f ((1 - δ) * a n) := by
    filter_upwards [hev] with n ⟨h2X0, ha_eq, hne, hbdd⟩ δ hδ hδ2
    by_contra hlt
    push Not at hlt
    have hX0le : X0 ≤ (1 - δ) * a n := by
      have ha2 : (2 : ℝ) * X0 ≤ a n := by rw [ha_eq]; exact h2X0
      have h2 : (1 : ℝ) / 2 * (2 * X0) ≤ (1 - δ) * a n :=
        mul_le_mul (by linarith) ha2 (by linarith [hX0]) (by linarith)
      have hX0eq : X0 = (1 : ℝ) / 2 * (2 * X0) := by ring
      rw [hX0eq]
      exact h2
    have hub : (1 - δ) * a n ∈ upperBounds (S n) := by
      rw [mem_upperBounds]
      intro x hx
      have hx' : (n : ℝ)⁻¹ ≤ f x := hx
      by_contra hgt
      push Not at hgt
      have hfx : f x ≤ f ((1 - δ) * a n) := hmono _ hX0le x (le_of_lt hgt)
      linarith
    have hle : sSup (S n) ≤ (1 - δ) * a n := csSup_le hne (mem_upperBounds.mp hub)
    rw [ha_eq] at hle
    have hapos : 0 < a n := ha_pos n
    nlinarith [hle, hapos, hδ]
  have hcont1 : ContinuousAt (fun δ : ℝ => (1 + δ) ^ α) 0 :=
    ContinuousAt.rpow (continuousAt_const.add continuousAt_id) continuousAt_const
      (Or.inl (by norm_num))
  have hcont2 : ContinuousAt (fun δ : ℝ => (1 - δ) ^ α) 0 :=
    ContinuousAt.rpow (continuousAt_const.sub continuousAt_id) continuousAt_const
      (Or.inl (by norm_num))
  refine ⟨a, ha_pos, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hmain : ∀ᶠ n in atTop, dist (↑n * f (a n)) 1 < ε := by
    obtain ⟨δ1, hδ1pos, hδ1⟩ := Metric.continuousAt_iff.mp hcont1 (ε / 2) (by linarith)
    obtain ⟨δ2, hδ2pos, hδ2⟩ := Metric.continuousAt_iff.mp hcont2 (ε / 2) (by linarith)
    set δ := min (1 / 2) (min δ1 δ2 / 2) with hδdef
    have hδpos : 0 < δ := lt_min (by norm_num) (div_pos (lt_min hδ1pos hδ2pos) (by norm_num))
    have hδle : δ ≤ 1 / 2 := min_le_left _ _
    have hδlt1 : δ < δ1 := by
      have h1 : min δ1 δ2 ≤ δ1 := min_le_left _ _
      have h2 : δ ≤ min δ1 δ2 / 2 := le_trans (min_le_right _ _) le_rfl
      linarith
    have hδlt2 : δ < δ2 := by
      have h1 : min δ1 δ2 ≤ δ2 := min_le_right _ _
      have h2 : δ ≤ min δ1 δ2 / 2 := le_trans (min_le_right _ _) le_rfl
      linarith
    have hbd1 : |(1 + δ) ^ α - 1| < ε / 2 := by
      have h := hδ1 (show dist δ 0 < δ1 from by
        rw [Real.dist_eq, sub_zero, abs_of_pos hδpos]; exact hδlt1)
      simp only [add_zero, Real.one_rpow] at h
      rw [Real.dist_eq] at h
      exact h
    have hbd2 : |(1 - δ) ^ α - 1| < ε / 2 := by
      have h := hδ2 (show dist δ 0 < δ2 from by
        rw [Real.dist_eq, sub_zero, abs_of_pos hδpos]; exact hδlt2)
      simp only [sub_zero, Real.one_rpow] at h
      rw [Real.dist_eq] at h
      exact h
    have hup : (1 + δ) ^ α < 1 + ε / 2 := by
      have h := abs_lt.mp hbd1
      linarith
    have hlow : 1 - ε / 2 < (1 - δ) ^ α := by
      have h := abs_lt.mp hbd2
      linarith
    have hratio1 : Tendsto (fun n => f ((1 + δ) * a n) / f (a n)) atTop
        (𝓝 ((1 + δ) ^ (-α))) :=
      (tendsto_ratio hL (eventually_atTop.mpr ⟨X0, fun x hx => hrepX x hx⟩)
        (c := 1 + δ) (by linarith)).comp ha_top
    have hratio2 : Tendsto (fun n => f ((1 - δ) * a n) / f (a n)) atTop
        (𝓝 ((1 - δ) ^ (-α))) :=
      (tendsto_ratio hL (eventually_atTop.mpr ⟨X0, fun x hx => hrepX x hx⟩)
        (c := 1 - δ) (by linarith)).comp ha_top
    have hpos_an : ∀ᶠ n in atTop, 0 < f (a n) := by
      filter_upwards [hev] with n ⟨h2X0, ha_eq, hne, hbdd⟩
      exact hposX _ (by rw [ha_eq]; linarith [h2X0, hX0])
    have hpos1 : ∀ᶠ n in atTop, 0 < f ((1 + δ) * a n) := by
      filter_upwards [hev] with n ⟨h2X0, ha_eq, hne, hbdd⟩
      apply hposX
      rw [ha_eq]
      have hle : sSup (S n) ≤ (1 + δ) * sSup (S n) :=
        le_mul_of_one_le_left (by linarith [h2X0, hX0]) (by linarith)
      linarith [h2X0, hX0, hle]
    have hpos2 : ∀ᶠ n in atTop, 0 < f ((1 - δ) * a n) := by
      filter_upwards [hev] with n ⟨h2X0, ha_eq, hne, hbdd⟩
      apply hposX
      rw [ha_eq]
      have h2 : (1 : ℝ) / 2 * (2 * X0) ≤ (1 - δ) * sSup (S n) :=
        mul_le_mul (by linarith) h2X0 (by linarith [hX0]) (by linarith)
      have hX0eq : X0 = (1 : ℝ) / 2 * (2 * X0) := by ring
      rw [hX0eq]
      exact h2
    have hinv1 : Tendsto (fun n => (f ((1 + δ) * a n) / f (a n))⁻¹) atTop
        (𝓝 ((1 + δ) ^ α)) := by
      have h := hratio1.inv₀ (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + δ) _).ne'
      rwa [Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 + δ), inv_inv] at h
    have hinv2 : Tendsto (fun n => (f ((1 - δ) * a n) / f (a n))⁻¹) atTop
        (𝓝 ((1 - δ) ^ α)) := by
      have h := hratio2.inv₀ (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 - δ) _).ne'
      rwa [Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 - δ), inv_inv] at h
    have hevU : ∀ᶠ n in atTop, (f ((1 + δ) * a n) / f (a n))⁻¹ < 1 + ε := by
      apply hinv1.eventually_lt_const
      linarith [hup, hε]
    have hevL : ∀ᶠ n in atTop, 1 - ε < (f ((1 - δ) * a n) / f (a n))⁻¹ := by
      apply hinv2.eventually_const_lt
      linarith [hlow, hε]
    filter_upwards [hev, hC1, hC2, hpos_an, hpos1, hpos2, hevU, hevL,
      eventually_ge_atTop 1] with n ⟨h2X0, ha_eq, hne, hbdd⟩ hC1n hC2n hfan hfp1
      hfp2 hU hL hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
    have hfne : f (a n) ≠ 0 := hfan.ne'
    have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
    have e : ((n : ℝ) * f (a n))⁻¹ * f (a n) = (n : ℝ)⁻¹ := by
      rw [mul_inv, mul_assoc, inv_mul_cancel₀ hfne, mul_one]
    have hr1 : f ((1 + δ) * a n) / f (a n) ≤ ((n : ℝ) * f (a n))⁻¹ := by
      rw [div_le_iff₀ hfan, e]
      exact hC1n δ hδpos
    have hr2 : ((n : ℝ) * f (a n))⁻¹ ≤ f ((1 - δ) * a n) / f (a n) := by
      rw [le_div_iff₀ hfan, e]
      exact hC2n δ hδpos hδle
    have hnf : (n : ℝ) * f (a n) ≤ (f ((1 + δ) * a n) / f (a n))⁻¹ :=
      (le_inv_comm₀ (mul_pos hnpos hfan) (div_pos hfp1 hfan)).mpr hr1
    have hnf2 : (f ((1 - δ) * a n) / f (a n))⁻¹ ≤ (n : ℝ) * f (a n) := by
      rw [← inv_inv ((n : ℝ) * f (a n))]
      exact (inv_le_inv₀ (div_pos hfp2 hfan) (inv_pos.mpr (mul_pos hnpos hfan))).mpr hr2
    rw [Real.dist_eq]
    rw [abs_lt]
    constructor <;> linarith
  exact eventually_atTop.mp hmain

end MathlibExt.Probability.RegularVariation

end
