/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.Probability

/-- The pushforward of a measure `P` under `ω ↦ (X ω, Y ω)`, for a.e.-measurable `X` and `Y`,
gives a measurable rectangle `s ×ˢ t` the measure `P (X ⁻¹' s ∩ Y ⁻¹' t)`. When `P` is a
probability measure this pushforward is the joint law of `X` and `Y`, and the value is the
probability that both events occur. -/
theorem map_prodMk_apply_prod
    {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {P : Measure Ω}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    {s : Set 𝓧} {t : Set 𝓨} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    P.map (fun ω => (X ω, Y ω)) (s ×ˢ t) = P (X ⁻¹' s ∩ Y ⁻¹' t) := by
  rw [Measure.map_apply_of_aemeasurable (hX.prodMk hY) (hs.prod ht)]
  rfl

end MathlibExt.Probability
