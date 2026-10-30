/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.RegularVariation
import MathlibExt.Probability.TruncatedMomentRV

open MeasureTheory Filter Set
open scoped Topology ENNReal
open MathlibExt.Probability.RegularVariation
open MathlibExt.Probability.TruncatedMoment

namespace MathlibExtTest.Probability.TruncatedMomentRVCanonical

-- An atom at either excluded boundary contributes to tailGe, not the strict tail.
example : combinedTail (Measure.dirac (-1 : ℝ)) 1 = 0 ∧
    tailGe (Measure.dirac (-1 : ℝ)) 1 = 1 ∧ tailGt (Measure.dirac (-1 : ℝ)) 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [combinedTail, rightTail, leftTail, tailGe, tailGt, Measure.dirac_apply]

example : combinedTail (Measure.dirac (1 : ℝ)) 1 = 0 ∧
    tailGe (Measure.dirac (1 : ℝ)) 1 = 1 ∧ tailGt (Measure.dirac (1 : ℝ)) 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [combinedTail, rightTail, leftTail, tailGe, tailGt, Measure.dirac_apply]

-- At zero the two endpoints coincide: that atom is counted only once.
example : combinedTail (Measure.dirac (0 : ℝ)) 0 = 0 ∧
    tailGe (Measure.dirac (0 : ℝ)) 0 = 1 ∧ tailGt (Measure.dirac (0 : ℝ)) 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [combinedTail, rightTail, leftTail, tailGe, tailGt, Measure.dirac_apply]

-- Negative thresholds have overlapping one-sided tails, so no global alias is valid.
example : combinedTail (Measure.dirac (0 : ℝ)) (-1) = 2 ∧
    tailGe (Measure.dirac (0 : ℝ)) (-1) = 1 ∧ tailGt (Measure.dirac (0 : ℝ)) (-1) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [combinedTail, rightTail, leftTail, tailGe, tailGt, Measure.dirac_apply]

private noncomputable def earlyFactor : ℝ → ℝ := fun x => if x ≤ 1 then -1 else 1

private theorem earlyFactor_slow : IsSlowlyVarying earlyFactor := by
  apply isSlowlyVarying_one.of_eventuallyEq
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp [earlyFactor, not_le.mpr hx]

example : IsSlowlyVarying earlyFactor ∧ earlyFactor (1 / 2) < 0 := by
  refine ⟨earlyFactor_slow, ?_⟩
  norm_num [earlyFactor]

-- Early factor values change the chosen factor, while regular variation is asymptotic.
example : IsRegularlyVarying (fun x => x ^ (-1 : ℝ) * earlyFactor x) (-1) := by
  apply (isRegularlyVarying_rpow (-1)).of_eventuallyEq
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp [earlyFactor, not_le.mpr hx]

-- Canonical callers obtain the genuine Potter/Karamata APIs directly.
example {W : ℝ → ℝ} {ρ : ℝ} (hW : Antitone W) (hWnn : ∀ t, 0 ≤ W t)
    (hWb : ∃ B, ∀ t, W t ≤ B) (hRV : IsRegularlyVarying W ρ)
    (hρ : ρ < 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C Y : ℝ, 0 < C ∧ 0 < Y ∧ ∀ x ≥ Y, ∀ u ∈ Set.Ioc 0 1,
      W (x * u) / W x ≤ C * u ^ (ρ - δ) :=
  potter_upper hW hWnn hWb hRV.eventually_pos (fun c hc => hRV.ratio_tendsto (c := c) hc) hρ hδ

example {W : ℝ → ℝ} {ρ β : ℝ} (hW : Antitone W) (hWnn : ∀ t, 0 ≤ W t)
    (hWb : ∃ B, ∀ t, W t ≤ B) (hRV : IsRegularlyVarying W ρ)
    (hρ : ρ < 0) (hβ : 0 ≤ β) (hβρ : 0 < β + 1 + ρ) :
    Tendsto (fun x => (∫ t in (0 : ℝ)..x, t ^ β * W t) / (x ^ (β + 1) * W x))
      atTop (𝓝 (1 / (β + 1 + ρ))) :=
  karamata_integral hW hWnn hWb hRV.eventually_pos (fun c hc => hRV.ratio_tendsto (c := c) hc)
    hρ hβ hβρ

-- The primary claim keeps every probability/range/interval/normalization guard.
example {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (hRV : IsRegularlyVarying (combinedTail μ) (-α)) :
    Tendsto (fun x => (∫ y in Set.Icc (-x) x, y ^ 2 ∂μ) / (x ^ 2 * combinedTail μ x))
      atTop (𝓝 (α / (2 - α))) :=
  truncatedMoment_tendsto hα hα2 hRV

example (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s) :
    tailGe μ s = combinedTail μ s + (μ {s}).toReal + (μ {-s}).toReal :=
  tailGe_eq_combinedTail_add_atoms μ hs

example (μ : Measure ℝ) [IsFiniteMeasure μ] {s : ℝ} (hs : 0 ≤ s) :
    tailGt μ s = combinedTail μ s :=
  tailGt_eq_combinedTail μ hs

-- Review regression: finite mass is enough; probability normalization is unnecessary.
example (μ : Measure ℝ) [IsFiniteMeasure μ] {s : ℝ} (hs : 0 < s) :
    tailGe μ s = combinedTail μ s + (μ {s}).toReal + (μ {-s}).toReal :=
  tailGe_eq_combinedTail_add_atoms μ hs

-- Total mass two, with a nonzero atom at each boundary.
example :
    tailGe (Measure.dirac (-1 : ℝ) + Measure.dirac (1 : ℝ)) 1 =
      combinedTail (Measure.dirac (-1 : ℝ) + Measure.dirac (1 : ℝ)) 1 +
        ((Measure.dirac (-1 : ℝ) + Measure.dirac (1 : ℝ)) {1}).toReal +
        ((Measure.dirac (-1 : ℝ) + Measure.dirac (1 : ℝ)) {-1}).toReal ∧
    tailGe (Measure.dirac (-1 : ℝ) + Measure.dirac (1 : ℝ)) 1 = 2 ∧
    combinedTail (Measure.dirac (-1 : ℝ) + Measure.dirac (1 : ℝ)) 1 = 0 := by
  refine ⟨tailGe_eq_combinedTail_add_atoms _ (by norm_num), ?_, ?_⟩ <;>
    norm_num [combinedTail, rightTail, leftTail, tailGe,
      Measure.add_apply, Measure.dirac_apply]

-- Zero mass is finite and is not a probability law.
example : tailGe (0 : Measure ℝ) 1 = combinedTail (0 : Measure ℝ) 1 +
      ((0 : Measure ℝ) {1}).toReal + ((0 : Measure ℝ) {-1}).toReal ∧
    tailGe (0 : Measure ℝ) 1 = 0 := by
  refine ⟨tailGe_eq_combinedTail_add_atoms _ (by norm_num), ?_⟩
  simp [tailGe]

-- Conditional zero-index API/type coverage, with an explicit regular-variation witness.
example {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hRV : IsRegularlyVarying (combinedTail μ) (- (0 : ℝ))) :
    Tendsto (fun x => tailGt μ x / combinedTail μ x) atTop (𝓝 1) :=
  tailGt_ratio_tendsto hRV

-- Neither downstream strict-tail API needs a positive index.
example {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hRV : IsRegularlyVarying (combinedTail μ) (-α)) :
    ∀ᶠ x in atTop, 0 < tailGt μ x :=
  eventually_pos_tailGt hRV

example {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hRV : IsRegularlyVarying (combinedTail μ) (-α)) :
    ∀ c > 0, Tendsto (fun x => tailGt μ (c * x) / tailGt μ x) atTop (𝓝 (c ^ (-α))) :=
  tailGt_ratio_limit hRV

end MathlibExtTest.Probability.TruncatedMomentRVCanonical
