/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FreeGroupHyperbolic
import MathlibExt.GroupTheory.HyperbolicGroup

namespace MathlibExtTest.GroupTheory.FreeGroupHyperbolic

open MathlibExt.GroupTheory.HyperbolicGroupWanted Metric

-- The empty free basis gives the word metric on the trivial group.
example : @IsDeltaHyperbolic (FreeGroup Empty)
    (⟨FreeGroup.of, FreeGroup.closure_range_of Empty⟩ :
      Group.Generators (FreeGroup Empty) Empty).normedGroup.toPseudoMetricSpace 0 :=
  freeGroup_isDeltaHyperbolic_zero Empty

-- A free basis of rank two witnesses word-hyperbolicity as a finitely generated group.
example : Group.IsHyperbolic (FreeGroup (Fin 2)) :=
  ⟨Fin 2, inferInstance, ⟨FreeGroup.of, FreeGroup.closure_range_of _⟩, 0,
    freeGroup_isDeltaHyperbolic_zero (Fin 2)⟩

noncomputable local instance natWordMetric : NormedGroup (FreeGroup ℕ) :=
  (⟨FreeGroup.of, FreeGroup.closure_range_of ℕ⟩ : Group.Generators (FreeGroup ℕ) ℕ).normedGroup

-- Even for an infinite basis, sharing an initial edge from a given vertex is transitive.
example (w x y z : FreeGroup ℕ) (hxy : 1 ≤ gromovProduct w x y) (hyz : 1 ≤ gromovProduct w y z) :
    1 ≤ gromovProduct w x z := by
  apply (le_min hxy hyz).trans
  simpa only [sub_zero] using (freeGroup_isDeltaHyperbolic_zero ℕ).four_point w x y z

end MathlibExtTest.GroupTheory.FreeGroupHyperbolic
