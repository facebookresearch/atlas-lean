/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceSmashClosed

/-!
# Precomposition under transported closed structures

An equivalence `E : C ≌ D` and a family of adjunctions `tensorLeft M ⊣ R M`
transport the monoidal closed structure from `C` to `D`. Precomposition in
that structure is the whiskered mate of the tensoring map induced by
`E.inverse.map f`. Compatibility of conjugation with both whiskerings gives
the formula for every target-category morphism.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe uC vC uD vD
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace OrthogonalIGeneratorProbe.Transport

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D]
  (E : C ≌ D) (R : C → C ⥤ C)
  (h : ∀ M : C, tensorLeft M ⊣ R M)

theorem nativePre {X X' : D} (f : X' ⟶ X) :
    letI := Monoidal.transport E
    letI := PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed.Primitive.monoidalClosed E R h
    MonoidalClosed.pre f =
      Functor.whiskerLeft E.inverse (Functor.whiskerRight
        (conjugateEquiv (h (E.inverse.obj X)) (h (E.inverse.obj X'))
          ((tensoringLeft C).map (E.inverse.map f))) E.functor) := by
  let := Monoidal.transport E
  let := PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed.Primitive.monoidalClosed E R h
  unfold MonoidalClosed.pre
  rw [PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed.Primitive.monoidalClosed_adjunction,
    PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed.Primitive.monoidalClosed_adjunction]
  change conjugateEquiv
      ((E.symm.toAdjunction.comp (h (E.inverse.obj X))).comp E.toAdjunction)
      ((E.symm.toAdjunction.comp (h (E.inverse.obj X'))).comp E.toAdjunction)
      (Functor.whiskerRight (Functor.whiskerLeft E.inverse
        ((tensoringLeft C).map (E.inverse.map f))) E.functor) = _
  rw [conjugateEquiv_whiskerRight]
  have hp := conjugateEquiv_whiskerLeft (h (E.inverse.obj X)) (h (E.inverse.obj X'))
    E.symm.toAdjunction ((tensoringLeft C).map (E.inverse.map f))
  exact congrArg (fun τ => Functor.whiskerLeft E.inverse τ) hp



end OrthogonalIGeneratorProbe.Transport
