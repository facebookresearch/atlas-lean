/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkBaselineReplacement
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyWeakEquivalences

/-!
# Rezk weakness of the baseline replacement unit

The functorial baseline replacement unit is a Rezk weak equivalence for every simplicial space.
Its levelwise realization weak equivalences give Reedy weakness, which implies weakness in the
Rezk class.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped Simplicial

namespace SimplicialSpace.OriginalUnitCSSWeak

/-- The actual unlocalized baseline unit is Rezk weak by its derived levelwise realization maps. -/
theorem baselineUnit_rezkWeak (X : SimplicialSpace.{u}) :
    rezkWeakEquivalences (RezkBaselineReplacement.unit.app X) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  have h : WeakEquivalence (RezkBaselineReplacement.unit.app X) :=
    (ReedyModel.weakEquivalence_iff _).mpr
      (fun n => (RezkBaselineReplacement.unit_components X n).2)
  exact reedyWeak_le_rezkWeak _ ((HomotopicalAlgebra.weakEquivalence_iff _).mp h)

end SimplicialSpace.OriginalUnitCSSWeak
