/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic
import MathlibExt.AlgebraicTopology.SimplicialSet.Presentable

/-!
# Local presentability of designated simplicial spaces

The ordinary `SimplicialSpace` category is locally presentable at its value
universe. Both the object and morphism universes of the outer simplex index
are lifted before applying native presheaf presentability. The resulting
certificate is transported through the actual index and carrier equivalences.

This theorem can be installed locally by consumers without choosing a model
structure or introducing a global presentability instance.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace SimplicialSpace

/-- The designated simplicial-space category is locally presentable at its value universe. -/
theorem isLocallyPresentable : IsLocallyPresentable.{u} SimplicialSpace.{u} := by
  let _ : IsLocallyPresentable.{u} SSet.{u} := SSet.isLocallyPresentable
  let J := ULiftHom.{u} (ULift.{u} SimplexCategory)
  let e : SimplexCategory ≌ J := ULiftHomULiftCategory.equiv SimplexCategory
  let E : SimplicialObject SSet.{u} ≌ (Jᵒᵖ ⥤ SSet.{u}) :=
    Equivalence.congrLeft (E := SSet.{u}) e.op
  let _ : IsLocallyPresentable.{u} (Jᵒᵖ ⥤ SSet.{u}) := inferInstance
  let _ : IsLocallyPresentable.{u} (SimplicialObject SSet.{u}) := E.symm.isLocallyPresentable
  exact SimplicialSpace.equivalenceSimplicialObject.symm.isLocallyPresentable

end SimplicialSpace
