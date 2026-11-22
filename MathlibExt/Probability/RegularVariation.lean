/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Regular variation

A slowly varying function is eventually positive and has ratio limit one under
positive rescaling. A regularly varying function is eventually a power times a
slowly varying factor. These are asymptotic properties and are preserved by
changing the function on an eventually avoided set.

This module supplies corrected definitions and supporting closure/tail lemmas
for the Lecture18 domain-of-attraction context in
`v1/Atlas/TheoryOfProbability/targets.yaml`. The archived `DomainAttraction.lean`
used global positivity, an inclusive left endpoint, and a totalized tail ratio.
Those three conventions are corrected here; the archived sources are preserved.

The strict left tail is `μ(Iio(-x))`. For finite measures at nonnegative
thresholds, its sum with the strict right tail is the real absolute-tail mass.
The helper definitions are real projections for all measures; probability and
absolute-tail interpretations are asserted only in their stated finite/domain
scope. Tail balance is defined for finite measures and requires an eventually
positive combined tail. In particular,
eventually zero combined tails, including Dirac masses, have no balance parameter.

The domain-of-attraction and three tail-asymptotic theorems left unproved in v1
are deferred. No stable-law or convolution theory is re-declared here.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace MathlibExt.Probability.RegularVariation

/-!
### Slowly varying functions
-/

/-- `L : ℝ → ℝ` is *slowly varying* (at infinity) if it is eventually positive at infinity
and `L (c * x) / L x → 1` as `x → ∞` for every `c > 0`. -/
def IsSlowlyVarying (L : ℝ → ℝ) : Prop :=
  (∀ᶠ x in atTop, 0 < L x) ∧
  ∀ c : ℝ, 0 < c → Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1)

/-- A positive function with a positive finite limit at infinity is slowly
varying: the ratio of the function at `c * x` and at `x` tends to `a / a = 1`. -/
theorem IsSlowlyVarying.of_tendsto {L : ℝ → ℝ} {a : ℝ}
    (hpos : ∀ᶠ x in atTop, 0 < L x) (hlim : Tendsto L atTop (𝓝 a)) (ha : 0 < a) :
    IsSlowlyVarying L := by
  refine ⟨hpos, fun c hc => ?_⟩
  have h2 : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have h3 : Tendsto (fun x => L (c * x)) atTop (𝓝 a) := hlim.comp h2
  have h4 := h3.div hlim (ne_of_gt ha)
  rw [div_self ha.ne'] at h4
  convert h4 using 1

/-- The constant function `1` is slowly varying. -/
theorem isSlowlyVarying_one : IsSlowlyVarying (fun _ => (1 : ℝ)) := by
  refine ⟨Filter.Eventually.of_forall (fun _ => one_pos), fun c _ => ?_⟩
  simp

/-- A positive constant function is slowly varying. -/
theorem isSlowlyVarying_const {c : ℝ} (hc : 0 < c) : IsSlowlyVarying (fun _ => c) := by
  refine ⟨Filter.Eventually.of_forall (fun _ => hc), fun d _ => ?_⟩
  simp [div_self hc.ne']

/-- Slowly varying functions are closed under multiplication. -/
theorem IsSlowlyVarying.mul {L₁ L₂ : ℝ → ℝ}
    (h₁ : IsSlowlyVarying L₁) (h₂ : IsSlowlyVarying L₂) :
    IsSlowlyVarying (fun x => L₁ x * L₂ x) := by
  refine ⟨?_, fun c hc => ?_⟩
  · filter_upwards [h₁.1, h₂.1] with x hx₁ hx₂
    exact mul_pos hx₁ hx₂
  · have h := (h₁.2 c hc).mul (h₂.2 c hc)
    simp only [mul_one] at h
    refine h.congr' ?_
    filter_upwards with x
    exact div_mul_div_comm _ _ _ _

/-- Slowly varying functions are closed under multiplication by a positive
constant. -/
theorem IsSlowlyVarying.const_mul {L : ℝ → ℝ} (hL : IsSlowlyVarying L) {c : ℝ}
    (hc : 0 < c) : IsSlowlyVarying (fun x => c * L x) := by
  refine ⟨?_, fun d hd => ?_⟩
  · filter_upwards [hL.1] with x hx
    exact mul_pos hc hx
  · have heq : (fun x => c * L (d * x) / (c * L x)) = fun x => L (d * x) / L x := by
      funext x
      exact mul_div_mul_left _ _ hc.ne'
    rw [heq]
    exact hL.2 d hd

/-- `fun x ↦ 1 + (1 + x)⁻¹` is slowly varying: it tends to the positive limit
`1` at infinity. -/
theorem isSlowlyVarying_one_add_inv :
    IsSlowlyVarying (fun x : ℝ => 1 + (1 + x)⁻¹) := by
  apply IsSlowlyVarying.of_tendsto (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    positivity) _ one_pos
  have h : Tendsto (fun x : ℝ => (1 + x)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => 1 + x) atTop atTop := by
      simpa [add_comm] using
        tendsto_atTop_add_const_right atTop (1 : ℝ)
          (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
    exact tendsto_inv_atTop_zero.comp h1
  simpa using tendsto_const_nhds.add h

/-- Slow variation is preserved by changing the function on an eventually avoided set. -/
theorem IsSlowlyVarying.of_eventuallyEq {f g : ℝ → ℝ}
    (hf : IsSlowlyVarying f) (hfg : f =ᶠ[atTop] g) : IsSlowlyVarying g := by
  refine ⟨?_, fun c hc => ?_⟩
  · filter_upwards [hf.1, hfg] with x hx hfx
    rwa [← hfx]
  · have hscale : Tendsto (fun x : ℝ => c * x) atTop atTop :=
      tendsto_id.const_mul_atTop hc
    have hscaled := hfg.comp_tendsto hscale
    apply (hf.2 c hc).congr'
    filter_upwards [hfg, hscaled] with x hx hcx
    change f (c * x) / f x = g (c * x) / g x
    change f (c * x) = g (c * x) at hcx
    rw [hx, hcx]

/-!
### Regularly varying functions
-/

/-- `f` is *regularly varying* with index `ρ` if it can be written as
`f x = x ^ ρ * L x` eventually as `x → ∞`, where `L` is slowly varying. -/
def IsRegularlyVarying (f : ℝ → ℝ) (ρ : ℝ) : Prop :=
  ∃ L : ℝ → ℝ, IsSlowlyVarying L ∧ ∀ᶠ x in atTop, f x = x ^ ρ * L x

/-- The power function `x ↦ x ^ ρ` is regularly varying of index `ρ`, with
slowly varying factor `1`. -/
theorem isRegularlyVarying_rpow (ρ : ℝ) :
    IsRegularlyVarying (fun x : ℝ => x ^ ρ) ρ := by
  refine ⟨fun _ => 1, isSlowlyVarying_one, Filter.Eventually.of_forall fun x => ?_⟩
  simp

/-- Regularly varying functions are closed under multiplication, with indices
adding. -/
theorem IsRegularlyVarying.mul {f g : ℝ → ℝ} {ρ σ : ℝ}
    (hf : IsRegularlyVarying f ρ) (hg : IsRegularlyVarying g σ) :
    IsRegularlyVarying (f * g) (ρ + σ) := by
  obtain ⟨L₁, hL₁, hev₁⟩ := hf
  obtain ⟨L₂, hL₂, hev₂⟩ := hg
  refine ⟨fun x => L₁ x * L₂ x, hL₁.mul hL₂, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ), hev₁, hev₂] with x hx hfx hgx
  simp only [Pi.mul_apply]
  rw [hfx, hgx, mul_mul_mul_comm, ← Real.rpow_add hx]

/-- Regularly varying functions are closed under multiplication by a positive
constant. -/
theorem IsRegularlyVarying.const_mul {f : ℝ → ℝ} {ρ : ℝ}
    (hf : IsRegularlyVarying f ρ) {c : ℝ} (hc : 0 < c) :
    IsRegularlyVarying (fun x => c * f x) ρ := by
  obtain ⟨L, hL, hev⟩ := hf
  refine ⟨fun x => c * L x, hL.const_mul hc, ?_⟩
  filter_upwards [hev] with x hx
  rw [hx]
  ring

/-- A positive constant multiple of a power function is regularly varying. -/
theorem isRegularlyVarying_const_mul_rpow {c ρ : ℝ} (hc : 0 < c) :
    IsRegularlyVarying (fun x : ℝ => c * x ^ ρ) ρ :=
  (isRegularlyVarying_rpow ρ).const_mul hc

/-- Regular variation is preserved under eventual equality at infinity. -/
theorem IsRegularlyVarying.of_eventuallyEq {f g : ℝ → ℝ} {ρ : ℝ}
    (hf : IsRegularlyVarying f ρ) (hfg : f =ᶠ[atTop] g) :
    IsRegularlyVarying g ρ := by
  obtain ⟨L, hL, hev⟩ := hf
  refine ⟨L, hL, ?_⟩
  filter_upwards [hfg, hev] with x hfx hfx'
  rw [← hfx, hfx']

/-- A regularly varying function is eventually positive. -/
theorem IsRegularlyVarying.eventually_pos {f : ℝ → ℝ} {ρ : ℝ}
    (hf : IsRegularlyVarying f ρ) : ∀ᶠ x in atTop, 0 < f x := by
  obtain ⟨L, hL, hev⟩ := hf
  filter_upwards [eventually_gt_atTop (0 : ℝ), hL.1, hev] with x hx hLx hfx
  rw [hfx]
  exact mul_pos (Real.rpow_pos_of_pos hx ρ) hLx

/-!
### Tails of a measure on `ℝ`
-/

/-- The real projection of `μ(Ioi x)`; it is the right-tail mass when `μ` is finite. -/
def rightTail (μ : Measure ℝ) (x : ℝ) : ℝ := (μ (Set.Ioi x)).toReal

/-- The real projection of the strict left tail `μ(Iio(-x))`, with mass interpretation
for finite measures. -/
def leftTail (μ : Measure ℝ) (x : ℝ) : ℝ := (μ (Set.Iio (-x))).toReal

/-- The sum of the strict right and left real-valued tail projections.
For a finite measure and `0 ≤ x`, this equals `μ {y | x < |y|}` as a real number.
At negative thresholds the two sets can overlap, so this is not the absolute-tail mass. -/
def combinedTail (μ : Measure ℝ) (x : ℝ) : ℝ := rightTail μ x + leftTail μ x

theorem combinedTail_apply (μ : Measure ℝ) (x : ℝ) :
    combinedTail μ x = rightTail μ x + leftTail μ x :=
  rfl

theorem rightTail_nonneg (μ : Measure ℝ) (x : ℝ) : 0 ≤ rightTail μ x :=
  ENNReal.toReal_nonneg

theorem leftTail_nonneg (μ : Measure ℝ) (x : ℝ) : 0 ≤ leftTail μ x :=
  ENNReal.toReal_nonneg

theorem combinedTail_nonneg (μ : Measure ℝ) (x : ℝ) : 0 ≤ combinedTail μ x :=
  add_nonneg (rightTail_nonneg μ x) (leftTail_nonneg μ x)

/-- The right tail is at most `1` for a probability measure. -/
theorem rightTail_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    rightTail μ x ≤ 1 := by
  have h : μ (Set.Ioi x) ≤ 1 := by
    calc μ (Set.Ioi x) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hle : (μ (Set.Ioi x)).toReal ≤ (1 : ℝ≥0∞).toReal :=
    (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.one_ne_top).2 h
  simpa [rightTail] using hle

/-- The left tail is at most `1` for a probability measure. -/
theorem leftTail_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    leftTail μ x ≤ 1 := by
  have h : μ (Set.Iio (-x)) ≤ 1 := by
    calc μ (Set.Iio (-x)) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hle : (μ (Set.Iio (-x))).toReal ≤ (1 : ℝ≥0∞).toReal :=
    (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.one_ne_top).2 h
  simpa [leftTail] using hle

/-- The combined tail is at most `2` for a probability measure. -/
theorem combinedTail_le_two (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    combinedTail μ x ≤ 2 := by
  calc combinedTail μ x = rightTail μ x + leftTail μ x := rfl
    _ ≤ 1 + 1 := add_le_add (rightTail_le_one μ x) (leftTail_le_one μ x)
    _ = 2 := by norm_num

/-- The right tail is antitone in the threshold. -/
theorem rightTail_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Antitone (rightTail μ) := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono (Set.Ioi_subset_Ioi hab))

/-- The left tail is antitone in the threshold. -/
theorem leftTail_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Antitone (leftTail μ) := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono (Set.Iio_subset_Iio (neg_le_neg hab)))

/-- The combined tail is antitone in the threshold. -/
theorem combinedTail_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Antitone (combinedTail μ) := by
  intro a b hab
  exact add_le_add (rightTail_antitone μ hab) (leftTail_antitone μ hab)

/-- The right tail is dominated by the combined tail. -/
theorem rightTail_le_combinedTail (μ : Measure ℝ) (x : ℝ) :
    rightTail μ x ≤ combinedTail μ x :=
  le_add_of_nonneg_right (leftTail_nonneg μ x)

/-- The left tail is dominated by the combined tail. -/
theorem leftTail_le_combinedTail (μ : Measure ℝ) (x : ℝ) :
    leftTail μ x ≤ combinedTail μ x :=
  le_add_of_nonneg_left (rightTail_nonneg μ x)

/-- Auxiliary convergence criterion: a nonnegative antitone function on `ℝ`
whose values at natural numbers tend to `0` tends to `0` at infinity. -/
private theorem tendsto_atTop_of_antitone_of_tendsto_nat {F : ℝ → ℝ}
    (hF0 : ∀ x, 0 ≤ F x) (hAnti : Antitone F)
    (hNat : Tendsto (fun n : ℕ => F n) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hNat ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hNat ε hε
  refine ⟨N, fun x hx => ?_⟩
  have h1 : F x ≤ F (N : ℝ) := hAnti hx
  have h2 : dist (F (N : ℝ)) 0 < ε := hN N le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hF0 _)] at h2 ⊢
  exact lt_of_le_of_lt h1 h2

/-- The right tail at natural-number thresholds tends to `0`, by continuity
from above for the decreasing sets `(n, ∞)`, whose intersection is empty. -/
private theorem tendsto_rightTail_nat (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ => rightTail μ n) atTop (𝓝 0) := by
  have hInter : ⋂ n : ℕ, Set.Ioi (n : ℝ) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false,
      not_forall]
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact ⟨n, not_lt.mpr hn.le⟩
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun n : ℕ => Set.Ioi (n : ℝ))
    (fun _ => MeasurableSet.nullMeasurableSet measurableSet_Ioi)
    (fun _ _ hnm => Set.Ioi_subset_Ioi (by exact_mod_cast hnm))
    ⟨0, measure_ne_top μ _⟩
  rw [hInter, measure_empty] at h
  have h2 : Tendsto (fun n : ℕ => (μ (Set.Ioi (n : ℝ))).toReal) atTop (𝓝 0) := by
    rw [← ENNReal.toReal_zero]
    exact (ENNReal.tendsto_toReal_iff (fun _ => measure_ne_top μ _)
      ENNReal.zero_ne_top).2 h
  simpa [rightTail] using h2

/-- The left tail at natural-number thresholds tends to `0`, by continuity
from above for the decreasing sets `(-∞, -n)`, whose intersection is empty. -/
private theorem tendsto_leftTail_nat (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ => leftTail μ n) atTop (𝓝 0) := by
  have hInter : ⋂ n : ℕ, Set.Iio (-(n : ℝ)) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_empty_iff_false, iff_false,
      not_forall]
    obtain ⟨n, hn⟩ := exists_nat_gt (-x)
    exact ⟨n, by
      have : (-(n : ℝ)) < x := by linarith
      exact not_lt.mpr this.le⟩
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun n : ℕ => Set.Iio (-(n : ℝ)))
    (fun _ => MeasurableSet.nullMeasurableSet measurableSet_Iio)
    (fun _ _ hnm => Set.Iio_subset_Iio (neg_le_neg (by exact_mod_cast hnm)))
    ⟨0, measure_ne_top μ _⟩
  rw [hInter, measure_empty] at h
  have h2 : Tendsto (fun n : ℕ => (μ (Set.Iio (-(n : ℝ)))).toReal) atTop (𝓝 0) := by
    rw [← ENNReal.toReal_zero]
    exact (ENNReal.tendsto_toReal_iff (fun _ => measure_ne_top μ _)
      ENNReal.zero_ne_top).2 h
  simpa [leftTail] using h2

/-- The right tail of a finite measure tends to `0` at infinity. -/
theorem tendsto_rightTail_atTop (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (rightTail μ) atTop (𝓝 0) :=
  tendsto_atTop_of_antitone_of_tendsto_nat (rightTail_nonneg μ) (rightTail_antitone μ)
    (tendsto_rightTail_nat μ)

/-- The left tail of a finite measure tends to `0` at infinity. -/
theorem tendsto_leftTail_atTop (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (leftTail μ) atTop (𝓝 0) :=
  tendsto_atTop_of_antitone_of_tendsto_nat (leftTail_nonneg μ) (leftTail_antitone μ)
    (tendsto_leftTail_nat μ)

/-- The combined tail of a finite measure tends to `0` at infinity. -/
theorem tendsto_combinedTail_atTop (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (combinedTail μ) atTop (𝓝 0) := by
  have h := (tendsto_rightTail_atTop μ).add (tendsto_leftTail_atTop μ)
  rw [add_zero] at h
  exact h.congr (fun x => (combinedTail_apply μ x).symm)

/-!
### Tail balance
-/

/-- Tail balance for a finite measure requires an eventually positive combined real tail
and a ratio limit. For probability measures this expresses `P(X > x) / P(|X| > x) → p`.
Finiteness prevents infinite source tails from collapsing through `toReal`; eventual
positivity prevents totalized division from accepting an eventual `0 / 0`. -/
def HasTailBalance (μ : Measure ℝ) [IsFiniteMeasure μ] (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧
  (∀ᶠ x in atTop, 0 < combinedTail μ x) ∧
  Tendsto (fun x => rightTail μ x / combinedTail μ x) atTop (𝓝 p)

/-- An eventually zero right tail has balance zero when the combined tail remains
positive eventually. -/
theorem hasTailBalance_zero_of_eventually_rightTail_eq_zero (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : ∀ᶠ x in atTop, rightTail μ x = 0)
    (hdenom : ∀ᶠ x in atTop, 0 < combinedTail μ x) : HasTailBalance μ 0 := by
  refine ⟨le_refl 0, by norm_num, hdenom, ?_⟩
  have hev : (fun x => rightTail μ x / combinedTail μ x) =ᶠ[atTop] fun _ => (0 : ℝ) := by
    filter_upwards [h] with x hx
    rw [hx, zero_div]
  exact (tendsto_congr' hev).2 tendsto_const_nhds

/-- An eventually zero denominator cannot define tail balance. -/
theorem not_hasTailBalance_of_eventually_combinedTail_eq_zero (μ : Measure ℝ) [IsFiniteMeasure μ]
    (p : ℝ)
    (hzero : ∀ᶠ x in atTop, combinedTail μ x = 0) : ¬ HasTailBalance μ p := by
  intro hbalance
  obtain ⟨x, hpos, hz⟩ := (hbalance.2.2.1.and hzero).exists
  rw [hz] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- Every Dirac mass has eventually zero combined tail, so has no tail-balance parameter. -/
theorem not_hasTailBalance_dirac (a p : ℝ) : ¬ HasTailBalance (Measure.dirac a) p := by
  apply not_hasTailBalance_of_eventually_combinedTail_eq_zero
  filter_upwards [eventually_ge_atTop |a|] with x hx
  have hr : Measure.dirac a (Set.Ioi x) = 0 := by
    rw [Measure.dirac_apply]
    exact Set.indicator_of_notMem (not_lt.mpr ((le_abs_self a).trans hx)) _
  have hl : Measure.dirac a (Set.Iio (-x)) = 0 := by
    have hnot : a ∉ Set.Iio (-x) :=
      not_lt.mpr ((neg_le_neg hx).trans (neg_abs_le a))
    rw [Measure.dirac_apply]
    exact Set.indicator_of_notMem hnot (fun _ : ℝ => (1 : ℝ≥0∞))
  simp only [combinedTail, rightTail, leftTail, hr, hl, ENNReal.toReal_zero, add_zero]

end MathlibExt.Probability.RegularVariation
