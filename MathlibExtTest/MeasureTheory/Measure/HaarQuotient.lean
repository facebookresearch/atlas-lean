/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Measure.HaarQuotient

@[expose] public section

open MeasureTheory
open scoped ENNReal

/-- Consumer with the original binders. -/
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun q : MulAction.orbitRel.Quotient H G =>
      ∫⁻ x, f ((x : G) * q.out) ∂μH :=
  HaarQuotient.measurable_lintegral_mul_out H hH μH f hf

/-- The zero function gives the zero function on the quotient. -/
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (H : Subgroup G) (μH : Measure H) :
    (fun q : MulAction.orbitRel.Quotient H G =>
      ∫⁻ x, (0 : G → ℝ≥0∞) ((x : G) * q.out) ∂μH) = 0 := by
  funext q
  simp
