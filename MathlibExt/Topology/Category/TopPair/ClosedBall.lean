/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import Mathlib.Topology.Category.TopPair

/-!
# Closed-ball pairs

General pseudo-metric sphere/closed-ball pair and its max-norm classical
cell specialization.
-/

@[expose] public section

open scoped Set.Notation

universe u v

namespace TopPair

noncomputable def closedBallPair {E : Type v} [PseudoMetricSpace E]
    (x : E) (r : ℝ) : TopPair.{max u v} :=
  TopPair.of
    (TopCat.ofHom
      ⟨ULift.map
          (Set.inclusion (Metric.sphere_subset_closedBall (x := x) (ε := r))),
        (Topology.IsEmbedding.uliftMap
            (Topology.IsEmbedding.inclusion
              (Metric.sphere_subset_closedBall (x := x)
                (ε := r)))).continuous⟩)
    (Topology.IsEmbedding.uliftMap
        (Topology.IsEmbedding.inclusion
          (Metric.sphere_subset_closedBall (x := x) (ε := r))))

theorem isClosedEmbedding_closedBallPair_map {E : Type v}
    [PseudoMetricSpace E] (x : E) (r : ℝ) :
    Topology.IsClosedEmbedding
      (closedBallPair (E := E) (x := x) (r := r)).map := by
  have h_closed : IsClosed (Metric.closedBall x r ↓∩ Metric.sphere x r) :=
    IsClosed.preimage_val Metric.isClosed_sphere
  have h : Topology.IsClosedEmbedding
      (Set.inclusion
        (Metric.sphere_subset_closedBall (x := x) (ε := r))) :=
    Topology.IsClosedEmbedding.inclusion _ h_closed
  exact Topology.IsClosedEmbedding.uliftMap h

end TopPair

namespace Topology.CWComplex

noncomputable abbrev classicalCellDiskPair (n : ℕ) : TopPair.{u} :=
  TopPair.closedBallPair (E := Fin n → ℝ) 0 1

theorem isClosedEmbedding_classicalCellDiskPair_map {n : ℕ} :
    Topology.IsClosedEmbedding (classicalCellDiskPair (n := n)).map :=
  TopPair.isClosedEmbedding_closedBallPair_map (E := Fin n → ℝ) 0 1

end Topology.CWComplex
