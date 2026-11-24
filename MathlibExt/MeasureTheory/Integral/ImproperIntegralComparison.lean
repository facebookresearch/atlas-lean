/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Comparison tests for improper integrals

The improper integral `∫_a^∞ f` converges when `b ↦ ∫_a^b f` has a finite limit as `b → ∞`.
Both tests assume that `f` and `g` are interval integrable on `[a, b]` for every `b ≥ a`. For a
function that is nonnegative on `[a, ∞)`, this convergence is equivalent to Lebesgue
integrability on `(a, ∞)`: see `MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_tendsto`
and `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`.

## Main results

* `improper_integral_comparison_test`: if `0 ≤ f ≤ g` on `[a, ∞)` and `∫_a^∞ g` converges, then
  `∫_a^∞ f` converges. The partial integrals of `f` are nondecreasing and bounded by the limit of
  those of `g`.
* `improper_integral_limit_comparison_test`: if `f, g > 0` on `[a, ∞)` and `f / g → L ≠ 0`, then
  `∫_a^∞ f` converges if and only if `∫_a^∞ g` converges.

## References

* Mathlib, `docs/undergrad.yaml`, "Single Variable Real Analysis / Integration", "comparison test
  for improper integrals".
* G. Hartman et al., *APEX Calculus*, §6.8, "Limit Comparison Test for Improper Integrals".
-/

@[expose] public section

open MeasureTheory Filter Set Topology

namespace MathlibExt.MeasureTheory.Integral.ImproperIntegralComparisonWanted

/-- Partial integrals of a nonnegative function are nondecreasing on `[a, ∞)`. -/
private lemma integral_mono_right_of_nonneg {f : ℝ → ℝ} {a : ℝ} (hf : ∀ x, a ≤ x → 0 ≤ f x)
    (hfi : ∀ b, a ≤ b → IntervalIntegrable f volume a b) {b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∫ x in a..b, f x ≤ ∫ x in a..c, f x :=
  intervalIntegral.integral_mono_interval le_rfl hab hbc
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx ↦ hf x hx.1.le) (hfi c (hab.trans hbc))

/-- Convergence of `∫_a^∞ f` does not depend on the lower endpoint. -/
private lemma exists_tendsto_iff_of_le {f : ℝ → ℝ} {a c : ℝ} (hac : a ≤ c)
    (hfi : ∀ b, a ≤ b → IntervalIntegrable f volume a b) :
    (∃ L, Tendsto (fun b ↦ ∫ x in a..b, f x) atTop (𝓝 L)) ↔
      ∃ L, Tendsto (fun b ↦ ∫ x in c..b, f x) atTop (𝓝 L) := by
  have heq : (fun b ↦ (∫ x in a..c, f x) + ∫ x in c..b, f x) =ᶠ[atTop]
      fun b ↦ ∫ x in a..b, f x := by
    filter_upwards [eventually_ge_atTop c] with b hcb
    refine intervalIntegral.integral_add_adjacent_intervals (hfi c hac) ?_
    exact (hfi b (hac.trans hcb)).mono_set (by
      rw [uIcc_of_le hcb, uIcc_of_le (hac.trans hcb)]
      exact Icc_subset_Icc_left hac)
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L - ∫ x in a..c, f x, ?_⟩
    refine (hL.sub_const (∫ x in a..c, f x)).congr' ?_
    filter_upwards [heq] with b hb
    rw [← hb]
    ring
  · rintro ⟨L, hL⟩
    exact ⟨(∫ x in a..c, f x) + L, (hL.const_add _).congr' heq⟩

/-- Comparison test for improper integrals: a nonnegative function dominated on
`[a, ∞)` by an improper-integrable function is itself improper-integrable.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Single Variable Real Analysis / Integration",
  entry "comparison test for improper integrals" (currently missing).
- https://mathbooks.unl.edu/Calculus/sec-5-11-comparison.html

Proves `Wanted` entry `improper_integral_comparison_test`.
-/
theorem improper_integral_comparison_test {f g : ℝ → ℝ} {a : ℝ}
    (hfg : ∀ x : ℝ, a ≤ x → 0 ≤ f x ∧ f x ≤ g x)
    (hfi : ∀ b : ℝ, a ≤ b → IntervalIntegrable f volume a b)
    (hgi : ∀ b : ℝ, a ≤ b → IntervalIntegrable g volume a b)
    (hg : ∃ L : ℝ, Tendsto (fun b ↦ ∫ x in a..b, g x) atTop (nhds L)) :
    ∃ L : ℝ, Tendsto (fun b ↦ ∫ x in a..b, f x) atTop (nhds L) := by
  obtain ⟨L, hL⟩ := hg
  have hf0 : ∀ x, a ≤ x → 0 ≤ f x := fun x hx ↦ (hfg x hx).1
  have hg0 : ∀ x, a ≤ x → 0 ≤ g x := fun x hx ↦ (hfg x hx).1.trans (hfg x hx).2
  -- The partial integrals of `g` stay below their limit `L`.
  have hGL : ∀ b, a ≤ b → ∫ x in a..b, g x ≤ L := fun b hab ↦
    ge_of_tendsto hL (eventually_atTop.2 ⟨b, fun c hbc ↦
      integral_mono_right_of_nonneg hg0 hgi hab hbc⟩)
  -- Extend the partial integrals of `f` by their value at `a` below `a`: a monotone function.
  set F : ℝ → ℝ := fun b ↦ ∫ x in a..max a b, f x
  have hFmono : Monotone F := fun b c hbc ↦
    integral_mono_right_of_nonneg hf0 hfi (le_max_left a b) (max_le_max le_rfl hbc)
  have hFbdd : BddAbove (range F) := by
    refine ⟨L, ?_⟩
    rintro _ ⟨b, rfl⟩
    exact (intervalIntegral.integral_mono_on (le_max_left a b) (hfi _ (le_max_left a b))
      (hgi _ (le_max_left a b)) fun x hx ↦ (hfg x hx.1).2).trans (hGL _ (le_max_left a b))
  refine ⟨⨆ b, F b, (tendsto_atTop_ciSup hFmono hFbdd).congr' ?_⟩
  filter_upwards [eventually_ge_atTop a] with b hab
  simp only [F, max_eq_right hab]

/-- Limit comparison test for improper integrals: two functions that are strictly positive on
`[a, ∞)` and whose ratio tends to a nonzero limit are improper-integrable together.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Single Variable Real Analysis / Integration",
  entry "comparison test for improper integrals" (currently missing).
- G. Hartman et al., *APEX Calculus*, §6.8, "Limit Comparison Test for Improper Integrals".

Proves `Wanted` entry `improper_integral_limit_comparison_test`.
-/
theorem improper_integral_limit_comparison_test
    {f g : ℝ → ℝ} {a : ℝ} {L : ℝ}
    (hf : ∀ x : ℝ, a ≤ x → 0 < f x)
    (hg : ∀ x : ℝ, a ≤ x → 0 < g x)
    (hfi : ∀ b : ℝ, a ≤ b → IntervalIntegrable f volume a b)
    (hgi : ∀ b : ℝ, a ≤ b → IntervalIntegrable g volume a b)
    (hL : L ≠ 0)
    (hlim : Tendsto (fun x ↦ f x / g x) atTop (nhds L)) :
    (∃ L' : ℝ, Tendsto (fun b ↦ ∫ x in a..b, f x) atTop (nhds L')) ↔
      ∃ L' : ℝ, Tendsto (fun b ↦ ∫ x in a..b, g x) atTop (nhds L') := by
  -- The limit is positive, so `L / 2 < f / g < 2 L` from some `c ≥ a` on.
  have hL0 : 0 < L := lt_of_le_of_ne
    (ge_of_tendsto hlim (eventually_atTop.2 ⟨a, fun x hx ↦ (div_pos (hf x hx) (hg x hx)).le⟩))
    hL.symm
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1
    (hlim.eventually (Ioo_mem_nhds (half_lt_self hL0) (by linarith : L < 2 * L)))
  set c := max a c₀
  have hac : a ≤ c := le_max_left a c₀
  have hcx : ∀ x, c ≤ x → a ≤ x := fun x hx ↦ hac.trans hx
  have hratio : ∀ x, c ≤ x → L / 2 < f x / g x ∧ f x / g x < 2 * L := fun x hx ↦
    hc₀ x ((le_max_right a c₀).trans hx)
  -- Integrability on `[c, b]` from integrability on `[a, b]`.
  have hsub : ∀ {h : ℝ → ℝ}, (∀ b, a ≤ b → IntervalIntegrable h volume a b) →
      ∀ b, c ≤ b → IntervalIntegrable h volume c b := fun hh b hcb ↦
    (hh b (hac.trans hcb)).mono_set (by
      rw [uIcc_of_le hcb, uIcc_of_le (hac.trans hcb)]
      exact Icc_subset_Icc_left hac)
  have hscale : ∀ {h : ℝ → ℝ} (r : ℝ), (∃ L', Tendsto (fun b ↦ ∫ x in c..b, h x) atTop (𝓝 L')) →
      ∃ L', Tendsto (fun b ↦ ∫ x in c..b, r * h x) atTop (𝓝 L') := by
    rintro h r ⟨L', hL'⟩
    exact ⟨r * L', by simpa only [intervalIntegral.integral_const_mul] using hL'.const_mul r⟩
  rw [exists_tendsto_iff_of_le hac hfi, exists_tendsto_iff_of_le hac hgi]
  constructor
  · -- `g ≤ (2 / L) f` on `[c, ∞)`.
    intro hF
    refine improper_integral_comparison_test (g := fun x ↦ 2 / L * f x)
      (fun x hx ↦ ⟨(hg x (hcx x hx)).le, ?_⟩) (hsub hgi) (fun b hb ↦ (hsub hfi b hb).const_mul _)
      (hscale _ hF)
    have hgx := hg x (hcx x hx)
    have h1 := (hratio x hx).1
    rw [lt_div_iff₀ hgx] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
    linarith
  · -- `f ≤ 2 L g` on `[c, ∞)`.
    intro hG
    refine improper_integral_comparison_test (g := fun x ↦ 2 * L * g x)
      (fun x hx ↦ ⟨(hf x (hcx x hx)).le, ?_⟩) (hsub hfi) (fun b hb ↦ (hsub hgi b hb).const_mul _)
      (hscale _ hG)
    have hgx := hg x (hcx x hx)
    have h2 := (hratio x hx).2
    rw [div_lt_iff₀ hgx] at h2
    linarith

end MathlibExt.MeasureTheory.Integral.ImproperIntegralComparisonWanted
