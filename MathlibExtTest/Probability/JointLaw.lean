/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.JointLaw
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory Set

-- Public use on a measurable rectangle, for an arbitrary measure `P`.
example {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (P : Measure Ω)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (s : Set 𝓧) (t : Set 𝓨) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    P.map (fun ω => (X ω, Y ω)) (s ×ˢ t) = P (X ⁻¹' s ∩ Y ⁻¹' t) :=
  MathlibExt.Probability.map_prodMk_apply_prod hX hY hs ht

-- Rectangle with a full second side: the pushforward of `P` under `X` (the marginal law of `X`
-- when `P` is a probability measure).
example {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (P : Measure Ω)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (s : Set 𝓧) (hs : MeasurableSet s) :
    P.map (fun ω => (X ω, Y ω)) (s ×ˢ univ) = P (X ⁻¹' s) := by
  simpa using MathlibExt.Probability.map_prodMk_apply_prod hX hY hs MeasurableSet.univ

-- Probability-measure case: the value is a probability.
example {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (s : Set 𝓧) (t : Set 𝓨) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    P.map (fun ω => (X ω, Y ω)) (s ×ˢ t) ≤ 1 := by
  rw [MathlibExt.Probability.map_prodMk_apply_prod hX hY hs ht]
  exact prob_le_one
