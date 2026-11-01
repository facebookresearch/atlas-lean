/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Group.BruhatSection

@[expose] public section

open scoped Pointwise

example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (T : Subgroup G) (hT : IsClosed (T : Set G))
    [MeasurableSpace T] [BorelSpace T] (τ : MeasureTheory.Measure T) [τ.IsHaarMeasure]
    [τ.IsMulRightInvariant] {E C : Set G} (hC : IsCompact C)
    (hE : E ⊆ (T : Set G) * C) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x ∈ E, ∫ t : T, w ((t : G) * x) ∂τ = 1 :=
  MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
    T hT τ hC hE
