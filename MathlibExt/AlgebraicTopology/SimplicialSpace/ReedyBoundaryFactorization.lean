/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGenerators

/-!
# Monomorphism/trivial-fibration factorization for Reedy boundaries

The named Reedy model factors every original simplicial-space map as an
original monomorphism followed by a map in the literal boundary RLP.  The
latter is exactly the named Reedy trivial-fibration class.  A selected boundary
therefore lifts against the right factor with both original square equations.
-/

set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra
open CategoryTheory.MorphismProperty

namespace SimplicialSpace.ReedyGeneratingFamilies

/-- The selected factorization from the named Reedy model, exposed with an
original monomorphism on the left and the literal boundary RLP on the right. -/
noncomputable def monoFactorizationData {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) : MapFactorizationData
      (monomorphisms SimplicialSpace.{u}) I.{u}.rlp f := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let d := MorphismProperty.factorizationData
    (cofibrations SimplicialSpace.{u}) (trivialFibrations SimplicialSpace.{u}) f
  refine
    { Z := d.Z
      i := d.i
      p := d.p
      fac := d.fac
      hi := (ReedyModel.cofibration_iff d.i).1
        ((HomotopicalAlgebra.cofibration_iff d.i).2 d.hi)
      hp := ?_ }
  rw [I_rlp_eq_trivialFibrations]
  exact d.hp

instance {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    Mono (monoFactorizationData f).i :=
  (monoFactorizationData f).hi

/-- Every literal Reedy boundary has the lifting property against a map in the
literal boundary RLP. -/
theorem boundary_hasLiftingProperty (b : BoundaryIndex)
    {X Y : SimplicialSpace.{u}} {p : X ⟶ Y} (hp : I.{u}.rlp p) :
    HasLiftingProperty (boundaryFamily.{u} b).hom p :=
  hp _ (MorphismProperty.ofHoms.mk b)

end SimplicialSpace.ReedyGeneratingFamilies
