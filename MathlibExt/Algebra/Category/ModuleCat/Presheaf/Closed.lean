/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @junekim623, Muse
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.MonoidalCompat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Closed tensor structure on presheaves of modules

Let R be a presheaf of commutative rings on a category C at the stated universe level. For
every R-module presheaf F, the functor M ↦ F ⊗_R M has a right adjoint. Thus there is an
internal Hom characterized by Hom(F ⊗_R M,N) ≅ Hom(M,Hom_R(F,N)).

The free-Yoneda separating family and preservation of colimits by tensoring give these
adjoints, hence the monoidal closed structure on the module-presheaf category.
-/

@[expose] public section

universe u

open _root_.CategoryTheory CategoryTheory MonoidalCategory Limits

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace PresheafOfModules

namespace ClosedAux

variable (R)

/-- Tensoring with a module presheaf is a left adjoint.

For a fixed R-module presheaf F, the functor M ↦ F ⊗_R M admits a right adjoint. -/
noncomputable instance isLeftAdjoint_tensorLeft
    (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})) :
    (tensorLeft F).IsLeftAdjoint := by
  exact isLeftAdjoint_of_preservesColimits_of_isSeparating.{u, u, u, u + 1, u + 1}
    (PresheafOfModules.freeYoneda.isSeparating
      (R ⋙ forget₂ CommRingCat RingCat.{u}))
    (tensorLeft F)

/-- The internal Hom adjunction for a module presheaf.

For F, use the right adjoint to tensoring on the left to obtain its closed-object structure,
characterized by Hom(F ⊗ M,N) ≅ Hom(M,Hom_R(F,N)). -/
noncomputable instance closedObj
    (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})) :
    Closed F where
  rightAdj := (tensorLeft F).rightAdjoint
  adj := Adjunction.ofIsLeftAdjoint (tensorLeft F)

end ClosedAux

/-- Module presheaves form a monoidal closed category.

Over a presheaf R of commutative rings, each left tensor functor has the internal Hom right
adjoint supplied by the closed-object construction. -/
noncomputable instance monoidalClosed :
    MonoidalClosed (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})) where
  closed F := ClosedAux.closedObj R F

end PresheafOfModules

end
