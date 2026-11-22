/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterArrowComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterAssociativity
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterMultiplication

/-!
# Original parameter-corner associativity over the same base

The native marked corner associator transports the same original slice
pushout points. Its target component is the actual three-coordinate
multiplication map, which retains the original last-coordinate base
projection. Hence the comparison is in the original fixed-base slice,
including for non-Kan bases, not merely in the absolute marked carrier.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory

namespace SSet.Marked

attribute [local instance] cartesianMonoidalCategory monoidalClosed
/-- The native marked product symmetry is used locally for the original slice-corner associator. -/
local instance overParameterCornerBraided : BraidedCategory Marked.{u} := .ofCartesianMonoidalCategory

/-- The actual underlying marked corners retain their original points and the native three-coordinate target
  comparison. -/
def overParameterUnderlyingAssociativityIso {Z : Marked.{u}} {A D K L : SSet.{u}} {X Y : Over Z}
    (a : A ⟶ D) (b : K ⟶ L) (f : X ⟶ Y) :
    Arrow.mk (overParameterPushoutProduct a (overParameterPushoutProduct b f)).left ≅
      Arrow.mk (overParameterPushoutProduct (Arrow.mk a □ Arrow.mk b).hom f).left := by
  let inner := overParameterPushoutProduct b f
  let e₁ := overParameterMarkedArrowIso a inner
  let e₂ := parameterPushoutProductCanonicalIso a inner.left
  let e₃ := (MonoidalCategory.Arrow.pushoutProduct.obj (Arrow.mk (maximal.map a))).mapIso
    (overParameterMarkedArrowIso b f)
  let e₄ := (parameterPushoutProductCanonicalIso a (parameterPushoutProduct b f.left)).symm
  let e₅ := parameterPushoutProductAssociativityIso a b f.left
  let e₆ := (overParameterMarkedArrowIso (Arrow.mk a □ Arrow.mk b).hom f).symm
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆

/-- The full target component is the same original marked product multiplication, retaining the
  last-coordinate projection. -/
theorem overParameterUnderlyingAssociativityIso_hom_right {Z : Marked.{u}} {A D K L : SSet.{u}} {X Y : Over Z}
    (a : A ⟶ D) (b : K ⟶ L) (f : X ⟶ Y) :
    (overParameterUnderlyingAssociativityIso a b f).hom.right =
      ((overParameterMultiplicationIso Z Y D L).hom).left := by
  apply Hom.ext
  rfl

/-- Both complete original scalar parameter corners are canonically isomorphic over the same supplied base. -/
def overParameterPushoutProductAssociativityIso {Z : Marked.{u}} {A D K L : SSet.{u}} {X Y : Over Z}
    (a : A ⟶ D) (b : K ⟶ L) (f : X ⟶ Y) :
    Arrow.mk (overParameterPushoutProduct a (overParameterPushoutProduct b f)) ≅
      Arrow.mk (overParameterPushoutProduct (Arrow.mk a □ Arrow.mk b).hom f) := by
  let i := overParameterPushoutProduct a (overParameterPushoutProduct b f)
  let j := overParameterPushoutProduct (Arrow.mk a □ Arrow.mk b).hom f
  let e := overParameterUnderlyingAssociativityIso a b f
  let r : prod (max D) (prod (max L) Y.left) ⟶ Z :=
    (overParameter Z (overParameter Z Y L) D).hom
  let r' : prod (max (D ⊗ L)) Y.left ⟶ Z := (overParameter Z Y (D ⊗ L)).hom
  have h : e.hom.right ≫ r' = r := by
    rw [overParameterUnderlyingAssociativityIso_hom_right]
    exact Over.w (overParameterMultiplicationIso Z Y D L).hom
  exact overArrowNormalizationIso i ≪≫ Arrow.isoOver e r r' h ≪≫
    (overArrowNormalizationIso j).symm

end SSet.Marked
