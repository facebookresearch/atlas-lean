/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.MetricSpace.PointedGromovHausdorffBorel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! Tests for the pointed GH Borel bridge on a constant Euclidean pair. -/

namespace PointedGromovHausdorffBorelTests

open Filter

example : TopologicalSpace.SeparableSpace (EuclideanSpace ℝ (Fin 2)) := inferInstance

example : BorelSpace (EuclideanSpace ℝ (Fin 2)) := inferInstance

theorem const_measurable_of_pointed :
    ∀ (R : ℝ) (hR : 0 < R) (ε : ℝ) (_ : 0 < ε),
      ∀ᶠ n in Filter.atTop,
        ∃ f : ↥(Metric.ball
          ((fun _ : ℕ => (0 : EuclideanSpace ℝ (Fin 2))) n) R) →
          EuclideanSpace ℝ (Fin 2), Measurable f ∧
            f ⟨(fun _ : ℕ => (0 : EuclideanSpace ℝ (Fin 2))) n,
              Metric.mem_ball_self hR⟩ = (0 : EuclideanSpace ℝ (Fin 2)) ∧
            (∀ x y,
              |dist (f x) (f y) - dist (x : EuclideanSpace ℝ (Fin 2))
                (y : EuclideanSpace ℝ (Fin 2))| ≤ ε) ∧
            Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (R - ε) ⊆
              Metric.thickening ε (Set.range f) := by
  have hconv : GromovHausdorff.PointedGHConverges
      (X := fun _ : ℕ => EuclideanSpace ℝ (Fin 2))
      (Y := EuclideanSpace ℝ (Fin 2))
      (fun _ : ℕ => (0 : EuclideanSpace ℝ (Fin 2)))
      (0 : EuclideanSpace ℝ (Fin 2)) := by
    apply GromovHausdorff.pointedGHConverges_const
  exact (GromovHausdorff.pointedGHConverges_iff_exists_measurable
      (X := fun _ : ℕ => EuclideanSpace ℝ (Fin 2))
      (Y := EuclideanSpace ℝ (Fin 2))
      (fun _ : ℕ => (0 : EuclideanSpace ℝ (Fin 2)))
      (0 : EuclideanSpace ℝ (Fin 2))).mp hconv

theorem const_pointed_of_measurable
    (h : ∀ (R : ℝ) (hR : 0 < R) (ε : ℝ) (_ : 0 < ε),
      ∀ᶠ n in Filter.atTop,
        ∃ f : ↥(Metric.ball
          ((fun _ : ℕ => (0 : EuclideanSpace ℝ (Fin 2))) n) R) →
          EuclideanSpace ℝ (Fin 2), Measurable f ∧
            f ⟨(fun _ : ℕ => (0 : EuclideanSpace ℝ (Fin 2))) n,
              Metric.mem_ball_self hR⟩ = (0 : EuclideanSpace ℝ (Fin 2)) ∧
            (∀ x y,
              |dist (f x) (f y) - dist (x : EuclideanSpace ℝ (Fin 2))
                (y : EuclideanSpace ℝ (Fin 2))| ≤ ε) ∧
            Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (R - ε) ⊆
              Metric.thickening ε (Set.range f)) :
    GromovHausdorff.PointedGHConverges
      (X := fun _ : ℕ => EuclideanSpace ℝ (Fin 2))
      (Y := EuclideanSpace ℝ (Fin 2))
      (fun _ : ℕ => (0 : EuclideanSpace ℝ (Fin 2)))
      (0 : EuclideanSpace ℝ (Fin 2)) :=
  (GromovHausdorff.pointedGHConverges_iff_exists_measurable
      (X := fun _ : ℕ => EuclideanSpace ℝ (Fin 2))
      (Y := EuclideanSpace ℝ (Fin 2))
      (fun _ : ℕ => (0 : EuclideanSpace ℝ (Fin 2)))
      (0 : EuclideanSpace ℝ (Fin 2))).mpr h

end PointedGromovHausdorffBorelTests
