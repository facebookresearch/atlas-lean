/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.FullEDecoratedMappingTower
import MathlibExt.AlgebraicTopology.SimplicialSpace.DecoratedWalkingIsomorphismStagePullback
import MathlibExt.AlgebraicTopology.SimplicialSpace.DecoratedOuterHornInduction
import MathlibExt.CategoryTheory.MorphismProperty.InverseTower
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous

/-!
# The original full-E forward evaluation is a trivial Kan fibration

The actual shifted decorated tower has trivial successor maps from the
original initial-horn restrictions. Its constructed limit and original
forward-edge isomorphism give the same canonical full-E evaluation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

namespace SimplicialSpace.FullEEquivalence

private theorem successor_trivialFibration (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (n : ℕ) :
    trivialFibrations SSet.{u}
      ((mappingTower W hW).map (homOfLE (Order.le_succ n)).op) := by
  have hh : trivialFibrations SSet.{u}
      (EquivalenceMapping.restriction W hW (SSet.horn (n + 2) 0).ι) := by
    cases n with
    | zero => exact DecoratedOuterTwoHorn.firstAllRestriction_trivialFibration W hW
    | succ n =>
      exact DecoratedOuterHorn.initialRestriction_trivialFibration W hW (n + 1 + 2) (by omega)
  have hp := (trivialFibrations SSet.{u}).of_isPullback
    (EquivalenceMapping.stageSuccessor_isPullback W hW (n + 2) (by omega)) hh
  rw [mappingTower_map]
  have he : n + 2 - 1 = n + 1 := by omega
  convert hp using 1
  congr!

/-- Evaluation on the original forward edge of the full walking isomorphism is a
trivial fibration against every original scalar monomorphism. -/
theorem forwardEvaluation_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    trivialFibrations SSet.{u} (evaluation W hW SSet.coherentIso.forwardMap) := by
  have hp : (cofibrations SSet.{u}).rlp ((mappingTowerCone W hW).π.app (op (0 : ℕ))) :=
    CategoryTheory.MorphismProperty.continuous_inverse_tower_rlp (cofibrations SSet.{u})
      (mappingTower W hW) (mappingTowerCone W hW) (mappingTowerIsLimit W hW) (by
        intro n _
        rw [cofibrations_rlp]
        exact successor_trivialFibration W hW n)
  rw [cofibrations_rlp] at hp
  have h := ((trivialFibrations SSet.{u}).cancel_right_of_respectsIso
    ((mappingTowerCone W hW).π.app (op (0 : ℕ))) (mappingTowerZeroIso W hW).hom).mpr hp
  rw [mappingTowerCone_zero] at h
  exact h

end SimplicialSpace.FullEEquivalence
