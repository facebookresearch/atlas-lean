/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.EulerTorus

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.EulerTorus`

* `IsTorusDefect ⊥ 0` on the one-vertex graph, with `bet_torusFaceCount_pos` and
  `bet_euler_torus` applied to it;
* `bet_euler_torus_planar` on the one-vertex graph;
* the defect bound has content: `δ = 3` is never a torus defect.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.EulerTorus

open _root_.StatMech _root_.StatMech.BeffaraDC

/-- The defect `0` is a torus defect of the empty graph on one vertex. -/
theorem bot_isTorusDefect : IsTorusDefect (⊥ : SimpleGraph (Fin 1)) 0 :=
  ⟨by norm_num, Nat.zero_le _⟩

-- The torus face count is positive.
example : 1 ≤ torusFaceCount (⊥ : SimpleGraph (Fin 1)) 0 :=
  bet_torusFaceCount_pos bot_isTorusDefect

-- The torus Euler relation for the one-vertex graph.
example : (Nat.card (Fin 1) : ℤ) - (⊥ : SimpleGraph (Fin 1)).edgeSet.ncard
    + torusFaceCount (⊥ : SimpleGraph (Fin 1)) 0
      = Nat.card (⊥ : SimpleGraph (Fin 1)).ConnectedComponent + 1 - 0 :=
  bet_euler_torus bot_isTorusDefect

-- The planar specialization.
example :
    torusFaceCount (⊥ : SimpleGraph (Fin 1)) 0 = Lattice.faceCount (⊥ : SimpleGraph (Fin 1)) :=
  (bet_euler_torus_planar _).1

-- A defect exceeding `2` is impossible.
example (G : SimpleGraph (Fin 3)) : ¬ IsTorusDefect G 3 := fun h => by
  have := h.le_two
  omega

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.EulerTorus
