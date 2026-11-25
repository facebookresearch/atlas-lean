/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import MathlibExt.CategoryTheory.Monoidal.PreservesColimits

/-!
# Actual colimit preservation for the full integer cochain tensor

Every tensor degree is its original ordinary coproduct of coefficient tensor
pieces. Coefficient tensoring and the coproduct functor preserve colimits, and
native cochain evaluation creates colimits. No support bound, field, flatness,
or tensor-colimit output premise is used.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

universe u v w

variable {R : Type u} [CommRing R]
variable [∀ X Y : GradedObject ℤ (ModuleCat.{u} R), GradedObject.HasTensor X Y]
variable [∀ X : ModuleCat.{u} R,
  PreservesColimit (Functor.empty.{0} (ModuleCat.{u} R))
    ((curriedTensor (ModuleCat.{u} R)).obj X)]
variable [∀ X : ModuleCat.{u} R,
  PreservesColimit (Functor.empty.{0} (ModuleCat.{u} R))
    ((curriedTensor (ModuleCat.{u} R)).flip.obj X)]
variable [∀ W X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasTensor₄ObjExt W X Y Z]
variable [∀ X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasGoodTensorTensor₂₃ X Y Z]
/-- The original full integer total-degree fiber. -/
abbrev intTensorTotalFiber (n : ℤ) :=
  (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⁻¹' {n}

/-- The actual original left tensor pieces in one integer degree. -/
def tensorLeftIntDegreePieces (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ Discrete (intTensorTotalFiber n) ⥤ ModuleCat.{u} R where
  obj L :=
    { obj := fun ij => K.X ij.as.val.1 ⊗ L.X ij.as.val.2
      map := fun f => eqToHom (by rw [Discrete.eq_of_hom f]) }
  map f :=
    { app := fun ij => K.X ij.as.val.1 ◁ f.f ij.as.val.2
      naturality := by
        intro i j g
        have hij : i = j := Discrete.ext (Discrete.eq_of_hom g)
        subst j
        simp }

set_option backward.isDefEq.respectTransparency false in
/-- Actual degree evaluation of the full cochain tensor is the original degree-piece coproduct. -/
def tensorLeftIntEvalIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    tensorLeft K ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n ≅
      tensorLeftIntDegreePieces K n ⋙ colim :=
  NatIso.ofComponents (fun _ => eqToIso (by rfl)) (fun {X Y} f => by
    dsimp
    apply GradedObject.mapObj_ext
    rintro ⟨p, q⟩ hi
    simp only [Category.comp_id, Category.id_comp]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    erw [colimit.ι_map]
    dsimp [tensorLeftIntDegreePieces]
    simp only [MonoidalCategory.id_whiskerRight, Category.id_comp]
    rfl)

/-- The actual original right tensor pieces in one integer degree. -/
def tensorRightIntDegreePieces (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ Discrete (intTensorTotalFiber n) ⥤ ModuleCat.{u} R where
  obj L :=
    { obj := fun ij => L.X ij.as.val.1 ⊗ K.X ij.as.val.2
      map := fun f => eqToHom (by rw [Discrete.eq_of_hom f]) }
  map f :=
    { app := fun ij => f.f ij.as.val.1 ▷ K.X ij.as.val.2
      naturality := by
        intro i j g
        have hij : i = j := Discrete.ext (Discrete.eq_of_hom g)
        subst j
        simp }

set_option backward.isDefEq.respectTransparency false in
/-- Actual degree evaluation of the full right cochain tensor is its original degree-piece
coproduct. -/
def tensorRightIntEvalIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    tensorRight K ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n ≅
      tensorRightIntDegreePieces K n ⋙ colim :=
  NatIso.ofComponents (fun _ => eqToIso (by rfl)) (fun {X Y} f => by
    dsimp
    apply GradedObject.mapObj_ext
    rintro ⟨p, q⟩ hi
    simp only [Category.comp_id, Category.id_comp]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    erw [colimit.ι_map]
    dsimp [tensorRightIntDegreePieces]
    simp only [MonoidalCategory.whiskerLeft_id]
    rw [Category.id_comp]
    rfl)

variable (J : Type w) [Category.{v} J] [HasColimitsOfShape J (ModuleCat.{u} R)]

/-- Each actual integer coefficient piece preserves colimits through native evaluation and
module tensoring. -/
instance tensorLeftIntDegreePieces_preservesColimits
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    PreservesColimitsOfShape J (tensorLeftIntDegreePieces K n) :=
  preservesColimitsOfShape_of_evaluation _ J (fun i => by
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) i.as.val.2 ⋙ tensorLeft (K.X i.as.val.1))
    infer_instance)

/-- The actual full integer left tensor functor preserves every supported colimit shape. -/
instance tensorLeftInt_preservesColimits
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesColimitsOfShape J (tensorLeft K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  apply preservesColimitsOfShape_of_natIso (tensorLeftIntEvalIso K n).symm

/-- Each actual integer right coefficient piece preserves colimits through native evaluation and
module tensoring. -/
instance tensorRightIntDegreePieces_preservesColimits
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    PreservesColimitsOfShape J (tensorRightIntDegreePieces K n) :=
  preservesColimitsOfShape_of_evaluation _ J (fun i => by
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) i.as.val.1 ⋙ tensorRight (K.X i.as.val.2))
    infer_instance)

/-- The actual full integer right tensor functor preserves every supported colimit shape. -/
instance tensorRightInt_preservesColimits
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesColimitsOfShape J (tensorRight K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  apply preservesColimitsOfShape_of_natIso (tensorRightIntEvalIso K n).symm

end CochainComplex
