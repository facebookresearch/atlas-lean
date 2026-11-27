/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.LocalClusteringCoefficient

/-! # Examples of local clustering coefficients -/

private def spokeOrChord (v w : Fin 5) : Prop := v = 0 ∨ w = 0 ∨ (v = 1 ∧ w = 2)

private def starWithChord : SimpleGraph (Fin 5) := SimpleGraph.fromRel spokeOrChord

private instance : DecidableRel starWithChord.Adj := fun v w => by
  haveI : Decidable (v ≠ w ∧ (spokeOrChord v w ∨ spokeOrChord w v)) := by
    unfold spokeOrChord
    infer_instance
  exact decidable_of_iff _ (SimpleGraph.fromRel_adj spokeOrChord v w).symm

-- Four neighbors, with just the edge joining 1 and 2 among them.
example : starWithChord.localClusteringCoefficient 0 = 1 / 6 := by decide +kernel

-- Vertex 3 has degree one, so there are no pairs of neighbors.
example : starWithChord.localClusteringCoefficient 3 = 0 := by decide +kernel

example : (⊤ : SimpleGraph (Fin 3)).localClusteringCoefficient 0 = 1 := by decide +kernel

example : (⊥ : SimpleGraph (Fin 1)).localClusteringCoefficient 0 = 0 := by decide +kernel
