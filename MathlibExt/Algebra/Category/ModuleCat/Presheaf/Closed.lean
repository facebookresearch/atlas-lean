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
# Monoidal closed structure for presheaves of modules

Each `tensorLeft F` is a left adjoint by the special adjoint functor theorem,
applied to the free-Yoneda separating family. This gives the monoidal closed
structure on presheaves of modules.
-/

@[expose] public section

universe u

open _root_.CategoryTheory CategoryTheory MonoidalCategory Limits

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace PresheafOfModules

namespace ClosedAux

variable (R)

/-- Each `tensorLeft F` is a left adjoint by the special adjoint functor
theorem, using the existing colimit preservation and the free-Yoneda
separating family.
Since Mathlib 4.34 the SAFT lemma is universe-polymorphic and needs
`WellPowered.{u} Cᵒᵖ`; this follows from the small detecting family
`freeYoneda` via `wellPowered_of_isDetecting` and `wellPowered_opposite`
(Mathlib's `PresheafOfModules.wellPowered` instance). -/
noncomputable instance isLeftAdjoint_tensorLeft
    (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})) :
    (tensorLeft F).IsLeftAdjoint := by
  exact isLeftAdjoint_of_preservesColimits_of_isSeparating.{u, u, u, u + 1, u + 1}
    (PresheafOfModules.freeYoneda.isSeparating
      (R ⋙ forget₂ CommRingCat RingCat.{u}))
    (tensorLeft F)

/-- Each object is closed, with right adjoint chosen from the SAFT instance. -/
noncomputable instance closedObj
    (F : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})) :
    Closed F where
  rightAdj := (tensorLeft F).rightAdjoint
  adj := Adjunction.ofIsLeftAdjoint (tensorLeft F)

end ClosedAux

/-- Monoidal closed structure on presheaves of modules over a presheaf of
commutative rings (small site). -/
noncomputable instance monoidalClosed :
    MonoidalClosed (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})) where
  closed F := ClosedAux.closedObj R F

end PresheafOfModules

end
