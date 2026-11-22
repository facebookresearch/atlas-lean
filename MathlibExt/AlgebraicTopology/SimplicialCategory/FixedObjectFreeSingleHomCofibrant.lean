/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModel
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeSingleHomLifting
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Genuine cofibrancy of the original free single-Hom objects

The same free single-Hom/evaluation adjunction transports the original
scalar initial lifting property into the actual fixed-object boundary
lifting class. The full free source and every original object label and
Hom simplex are retained, with no cofibrancy outcome supplied as input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeSingleHom
variable {O : Type u} (x y : O) (X : SSet.{u})
attribute [local instance] FixedObjectModel.modelCategory

/-- The SAME original single-Hom free object is genuinely cofibrant in the original fixed-object model. -/
theorem isCofibrant : IsCofibrant (object x y X) := by
  change Cofibration (initial.to (object x y X))
  rw [HomotopicalAlgebra.cofibration_iff]
  change (boundaryFamily O).rlp.llp (initial.to (object x y X))
  intro A B p hp
  have hscalar : SSet.modelCategoryQuillen.I.rlp (homMap p x y) :=
    (boundaryFamily_rlp_iff p).mp hp x y
  have hmono : (MorphismProperty.monomorphisms SSet.{u}).rlp (homMap p x y) := by
    rwa [SSet.rlp_monomorphisms]
  have hlift : HasLiftingProperty (initial.to X) (homMap p x y) :=
    hmono _ (inferInstance : Mono (initial.to X))
  let hfree : HasLiftingProperty ((functor x y).map (initial.to X)) p :=
    (hasLiftingProperty_free_iff x y (initial.to X) p).mpr hlift
  let _ : (functor x y).IsLeftAdjoint := (adjunction x y).isLeftAdjoint
  have hI : IsInitial ((functor x y).obj (⊥_ SSet.{u})) :=
    initialIsInitial.isInitialObj (functor x y) (⊥_ SSet.{u})
  let e := IsInitial.uniqueUpToIso initialIsInitial hI
  let ei : Arrow.mk (initial.to (object x y X)) ≅
      Arrow.mk ((functor x y).map (initial.to X)) :=
    Arrow.isoMk e (Iso.refl _) (initialIsInitial.hom_ext _ _)
  exact HasLiftingProperty.of_arrow_iso_left ei.symm p

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeSingleHom
