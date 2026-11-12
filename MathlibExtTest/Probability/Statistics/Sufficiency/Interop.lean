/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Interop

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.Sufficiency
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.Statistics.Sufficiency.Interop

/-- The identity statistic is sufficient for every finite family, through the bridge. -/
example {Θ X : Type*} [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (P : Θ → PMF X) :
    IsSufficient (MeasurableSpace.comap (id : X → X) ‹MeasurableSpace X›)
      fun θ => (P θ).toMeasure := by
  refine IsSufficientPMF.isSufficient_comap (T := id) ?_
  intro θ θ' x h h'
  simp only [PMF.map_id, id_eq] at h h' ⊢
  rw [ENNReal.div_self h (PMF.apply_ne_top _ _), ENNReal.div_self h' (PMF.apply_ne_top _ _)]

/-- Negative check: a constant statistic discards the observation and is not sufficient for
the two point masses on `Bool`. -/
example : ¬ IsSufficientPMF (fun b : Bool => PMF.pure b) (fun _ : Bool => ()) := by
  intro hT
  have h1 : (PMF.pure true).map (fun _ : Bool => ()) () ≠ 0 := by simp [PMF.pure_map]
  have h2 : (PMF.pure false).map (fun _ : Bool => ()) () ≠ 0 := by simp [PMF.pure_map]
  have h := hT true false true h1 h2
  simp [PMF.pure_map, PMF.pure_apply] at h

/-- `n = 0`: on a one-point observation space every statistic is sufficient. -/
example {Θ : Type*} (P : Θ → PMF Unit) : IsSufficientPMF P (fun _ : Unit => ()) := by
  change IsSufficientPMF P id
  intro θ θ' x h h'
  simp only [PMF.map_id, id_eq] at h h' ⊢
  rw [ENNReal.div_self h (PMF.apply_ne_top _ _), ENNReal.div_self h' (PMF.apply_ne_top _ _)]

end MathlibExtTest.Probability.Statistics.Sufficiency.Interop
