/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Action.Arrow
public import MathlibExt.CategoryTheory.Monoidal.EquivariantProfileCells

/-!
# The actual unary coefficient orbit of a tensor map

The positive one-input family retains its arbitrary original coefficient.
Its product-Sigma group is genuinely trivial, so both original quotient
projections and the original one-input pushout product give a whole Arrow
isomorphism to the actual left tensor map.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty CategoryTheory.OperadicOrbitCells

namespace HomotopicalAlgebra.ModuleTransfer.UnaryTensorOrbit

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{w, w} C]

/-- The original unary family is weighted by the actual arbitrary coefficient. -/
def family (N : C) {X Y : C} (f : X ⟶ Y) : PositiveOrbitFamily C :=
  { unaryOrbitFamily f with
    coefficient := Action.trivial (MultiplicityGroup (fun _ : Fin 1 => 1)) N }

/-- Both actual orbit projections normalize to the original tensor Arrow. -/
def tensorArrowIso (N : C) {X Y : C} (f : X ⟶ Y) :
    familyOrbitArrow (family N f) ≅ Arrow.mk (N ◁ f) := by
  let : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeOfUnivLE.{w, w} C
  let n := fun _ : Fin 1 => 1
  let : HasColimitsOfShape (SingleObj (MultiplicityGroup n)) C :=
    HasColimitsOfShape.of_essentiallySmall C _
  let a := matrixPushoutProductAction (by decide : 0 < 1) n (fun _ => Arrow.mk f)
  let B := Action.trivial (MultiplicityGroup n) N
  let : Subsingleton (MultiplicityGroup n) := inferInstance
  let e : coefficientUnderlyingArrow B (Action.actionUnderlyingHom a) ≅
      coefficientOrbitArrow B (Action.actionUnderlyingHom a) := coefficientOrbitTrivialGroupIso B _
  exact e.symm ≪≫ (tensorLeft N).mapArrow.mapIso (eqToIso (unaryPushoutProductAction_V f))

/-- The actual arbitrary-coefficient unary tensor map enters every iso-stable full orbit target class. -/
theorem tensor_mem (P Q : MorphismProperty C) [Q.RespectsIso] (h : orbitGenerators P ≤ Q)
    (N : C) {X Y : C} (f : X ⟶ Y) (hf : P f) : Q (N ◁ f) := by
  have hOrbit : orbitGenerators P (familyOrbitArrow (family N f)).hom :=
    familyOrbitArrow_mem P (family N f) (fun _ => hf)
  exact (Q.arrow_mk_iso_iff (tensorArrowIso N f)).mp (h _ hOrbit)

end HomotopicalAlgebra.ModuleTransfer.UnaryTensorOrbit
