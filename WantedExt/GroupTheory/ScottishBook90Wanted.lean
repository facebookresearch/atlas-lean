/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Topology.Connected.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.ScottishBook90Wanted

/--
Every connected semi-simple Lie group has two elements generating a dense
subgroup, so the number 4 in the Scottish Book statement can be lowered to 2.
Source: S. Ulam and H. Auerbach, Problem 90 of the Scottish Book (every
semi-simple Lie group contains four elements generating a dense subgroup;
can the number 4 be lowered?); Mauldin commentary: every connected
semi-simple Lie group has a free subgroup with two generators, and such a
free subgroup can be chosen dense.
-/
theorem_wanted semisimpleLieGroup_twoGeneratorsDense :
    ∀ (n : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) G]
      [LieGroup (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ⊤ G]
      [ConnectedSpace G]
      [LieAlgebra.IsSemisimple ℝ
        (GroupLieAlgebra (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) G)],
      ∃ a b : G,
        Dense (Subgroup.closure {a, b} : Set G)

end MathlibExt.GroupTheory.ScottishBook90Wanted
