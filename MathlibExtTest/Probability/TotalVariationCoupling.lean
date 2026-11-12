/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TotalVariationCoupling

/-- Boundary check: distance from a law to itself is `0`. -/
example {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (p : PMF α) : tvDist p p = 0 := by
  simp [tvDist]

/-- A maximal coupling exists for the pair `(p, p)`, and its
differing probability equals the (zero) total variation, as a
statement instance. -/
example {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (p : PMF α) :
    ∃ r : PMF (α × α), IsCoupling p p r ∧
      (r.toMeasure {x : α × α | x.1 ≠ x.2}).toReal = tvDist p p :=
  exists_maximal_coupling p p
