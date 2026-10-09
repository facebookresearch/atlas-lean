/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Shared helpers

Small facts used across the chapters of the entry.
-/

open MeasureTheory

namespace CDIS

/-- The law of an almost everywhere measurable map under a probability is a probability. -/
lemma isProbabilityMeasure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → β} (hf : AEMeasurable f μ) :
    IsProbabilityMeasure (μ.map f) :=
  (Measure.isProbabilityMeasure_map_iff hf).2 ‹_›

end CDIS
