/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Topology.MetricSpace.CompactCover
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.Algebra.Ring.Real

@[expose] public section

/-!
# Canonical metric and cover specialization for the finite standard simplex

The weights embedding induces a canonical `MetricSpace` on
`Convexity.StdSimplex ℝ (Fin (n + 1))` preserving the existing topology,
plus the `n / (n + 1)` diameter-subordination specialization of the neutral
compact-cover theorem.
-/

namespace Convexity.StdSimplex

/-- Canonical weights-induced metric on the finite simplex.

Built by pulling back the Pi-space metric along `t ↦ t.weights` through
`isEmbedding_toFun_comp_weights.comapMetricSpace`, which preserves the existing
canonical `TopologicalSpace` via `replaceTopology`. -/
noncomputable instance {n : ℕ} : MetricSpace (StdSimplex ℝ (Fin (n + 1))) :=
  (isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).comapMetricSpace
    (fun t ↦ t.weights : StdSimplex ℝ (Fin (n + 1)) → Fin (n + 1) → ℝ)

/-- Distance in the simplex is the Pi-space distance of the weights. -/
@[simp]
theorem dist_eq_weights {n : ℕ} (x y : StdSimplex ℝ (Fin (n + 1))) :
    dist x y = dist (x.weights : Fin (n + 1) → ℝ) (y.weights : Fin (n + 1) → ℝ) :=
  rfl

/-- Iterated-diameter subordinate cover for the finite simplex with factor
`n / (n + 1)`: some iterate makes every nonempty set of controlled diameter
subordinate to a given open cover. -/
theorem exists_iterate_diam_subordinate (n : ℕ) {X : Type*}
    [TopologicalSpace X]
    (g : C(StdSimplex ℝ (Fin (n + 1)), X)) {ι : Sort*} (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    ∃ k : ℕ, ∀ s : Set (StdSimplex ℝ (Fin (n + 1))),
      s.Nonempty →
      Metric.diam s ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ k *
        Metric.diam (Set.univ : Set (StdSimplex ℝ (Fin (n + 1)))) →
      ∃ i, g '' s ⊆ U i := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hq0 : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg _) hpos.le
  have hq1 : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
    (div_lt_one hpos).mpr (lt_add_of_pos_right _ one_pos)
  have hC : (0 : ℝ) ≤ Metric.diam (Set.univ : Set (StdSimplex ℝ (Fin (n + 1)))) :=
    Metric.diam_nonneg
  exact Metric.exists_pow_mul_diam_subordinate_of_compact _ _ hq0 hq1 hC g U hUopen hUcover

end Convexity.StdSimplex
