/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.ScottishBook170

open MeasureTheory Set
open MathlibExt.MeasureTheory.ScottishBook170Wanted

-- The plane measure induced by length on the horizontal axis detects one-dimensional
-- measurability, even though every subset of the axis has zero planar area.
example (A : Set ℝ)
    (h : ∀ T : Set (ℝ × ℝ), Nonempty (↥((fun x : ℝ => (x, (0 : ℝ))) '' A) ≃ₜ ↥T) →
      MeasurableSet[(volume : Measure (ℝ × ℝ)).toOuterMeasure.caratheodory] T) :
    MeasurableSet[(volume : Measure ℝ).toOuterMeasure.caratheodory] A := by
  let f (x : ℝ) := (x, (0 : ℝ))
  have hf : MeasurableEmbedding f := measurableEmbedding_prod_mk_right 0
  have haxis := szpilrajn170_homeomorphic_images_measurable_imp_absolute (f '' A) h
    ((volume : Measure ℝ).map f)
  intro t
  simpa only [Measure.toOuterMeasure_apply, hf.map_apply, preimage_inter, preimage_sdiff,
    hf.injective.preimage_image] using haxis (f '' t)

-- Every planar copy of a compact set is compact, so the hypothesis has concrete witnesses
-- for every Borel measure, including measures of infinite total mass.
example {S : Set (ℝ × ℝ)} (hS : IsCompact S) (μ : Measure (ℝ × ℝ)) :
    MeasurableSet[μ.toOuterMeasure.caratheodory] S := by
  apply szpilrajn170_homeomorphic_images_measurable_imp_absolute S _ μ
  rintro T ⟨e⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hT : IsCompact T := isCompact_iff_compactSpace.mpr e.compactSpace
  exact le_toOuterMeasure_caratheodory _ _ hT.measurableSet
