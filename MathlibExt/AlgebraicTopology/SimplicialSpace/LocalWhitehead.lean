/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyTwoTestDetector
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyWeakEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero

/-!
# Rezk and Reedy weak equivalences between complete Segal spaces

The original all-CSS weak test, the scalar component bijection, and the raw
two-test detector give the forward direction. The original-arrow Reedy
inclusion gives the converse under the same named Reedy model.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped SimplicialSpace.Inner
namespace SimplicialSpace

/-- Between the original complete Segal endpoints, Rezk and Reedy weakness agree. -/
theorem rezkWeak_iff_reedyWeak_of_completeSegalSpaces
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (hX : completeSegalSpaces X) (hY : completeSegalSpaces Y) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    rezkWeakEquivalences f ↔ WeakEquivalence f := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  constructor
  · intro hf
    exact reedyWeak_of_surjective_injective_mapπ₀ f
      (SSet.realizationWeakEquivalences.bijective_mapπ₀ (hf X hX)).2
      (SSet.realizationWeakEquivalences.bijective_mapπ₀ (hf Y hY)).1
  · intro hf
    exact reedyWeak_le_rezkWeak f
      ((HomotopicalAlgebra.weakEquivalence_iff f).1 hf)

end SimplicialSpace
