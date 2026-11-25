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

public import Mathlib.Algebra.Homology.Additive
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedSingle

/-!
# Naturality of bounded single complexes

The canonical comparison for mapping single complexes lifts to bounded
cochain complexes. Its components use the evaluation charts in the
support degree and vanish in every other degree. The comparisons satisfy
identity and composition laws.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uC vC uD vD uE vE

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.Bounded

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C] [HasZeroObject C]
variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D] [HasZeroObject D]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- Comparison for mapping single complexes in the bounded category. -/
def singleMapCochainComplexBounded (j : ℤ) :
    single C j ⋙ F.mapCochainComplexBounded ≅ F ⋙ single D j :=
  NatIso.ofComponents
    (fun X => (CochainComplex.bounded D).isoMk
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) j).app X))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) j).hom.naturality f)

/-- Underlying forward map of the bounded single-complex comparison. -/
theorem singleMapCochainComplexBounded_hom_app_hom (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded F j).hom.app X).hom =
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) j).hom.app X := rfl

/-- Underlying inverse map of the bounded single-complex comparison. -/
theorem singleMapCochainComplexBounded_inv_app_hom (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded F j).inv.app X).hom =
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) j).inv.app X := rfl

/-- Forward component in the support degree, expressed through evaluation charts. -/
@[simp]
theorem singleMapCochainComplexBounded_hom_app_self (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded F j).hom.app X).hom.f j =
      F.map (singleObjXSelf C j X).hom ≫ (singleObjXSelf D j (F.obj X)).inv :=
  HomologicalComplex.singleMapHomologicalComplex_hom_app_self F (.up ℤ) j X

/-- The forward comparison component is zero away from the support degree. -/
@[simp]
theorem singleMapCochainComplexBounded_hom_app_ne {i j : ℤ} (h : i ≠ j) (X : C) :
    ((singleMapCochainComplexBounded F j).hom.app X).hom.f i = 0 :=
  HomologicalComplex.singleMapHomologicalComplex_hom_app_ne F (.up ℤ) h X

/-- Inverse component in the support degree, expressed through evaluation charts. -/
@[simp]
theorem singleMapCochainComplexBounded_inv_app_self (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded F j).inv.app X).hom.f j =
      (singleObjXSelf D j (F.obj X)).hom ≫ F.map (singleObjXSelf C j X).inv :=
  HomologicalComplex.singleMapHomologicalComplex_inv_app_self F (.up ℤ) j X

/-- The inverse comparison component is zero away from the support degree. -/
@[simp]
theorem singleMapCochainComplexBounded_inv_app_ne {i j : ℤ} (h : i ≠ j) (X : C) :
    ((singleMapCochainComplexBounded F j).inv.app X).hom.f i = 0 :=
  HomologicalComplex.singleMapHomologicalComplex_inv_app_ne F (.up ℤ) h X

omit [HasZeroObject D] in
/-- Mapping a single complex preserves its support window `[j,j]`. -/
theorem singleMapCochainComplexBounded_source_isZero_X (j : ℤ) (X : C)
    (i : ℤ) (h : i ≠ j) :
    IsZero (((single C j ⋙ F.mapCochainComplexBounded).obj X).obj.X i) :=
  F.map_isZero (single_isZero_X C j X i h)

/-- Identity law for the bounded single-complex comparison. -/
theorem singleMapCochainComplexBounded_id_hom_app (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded (𝟭 C) j).hom.app X).hom =
      (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app ((single C j).obj X).obj :=
  HomologicalComplex.singleMapHomologicalComplex_id_hom_app (.up ℤ) j X

/-- Inverse identity law for the bounded single-complex comparison. -/
theorem singleMapCochainComplexBounded_id_inv_app (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded (𝟭 C) j).inv.app X).hom =
      (Functor.mapHomologicalComplexIdIso C (.up ℤ)).inv.app ((single C j).obj X).obj :=
  HomologicalComplex.singleMapHomologicalComplex_id_inv_app (.up ℤ) j X

variable {E : Type uE} [Category.{vE} E] [HasZeroMorphisms E] [HasZeroObject E]
variable (G : D ⥤ E) [G.PreservesZeroMorphisms]

/-- Composition law for the forward comparison maps. -/
theorem singleMapCochainComplexBounded_comp_hom_app (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded (F ⋙ G) j).hom.app X).hom =
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app
          ((single C j).obj X).obj ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((singleMapCochainComplexBounded F j).hom.app X).hom ≫
        ((singleMapCochainComplexBounded G j).hom.app (F.obj X)).hom :=
  HomologicalComplex.singleMapHomologicalComplex_comp_hom_app F G (.up ℤ) j X

/-- Composition law for the inverse comparison maps. -/
theorem singleMapCochainComplexBounded_comp_inv_app (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded (F ⋙ G) j).inv.app X).hom =
      ((singleMapCochainComplexBounded G j).inv.app (F.obj X)).hom ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((singleMapCochainComplexBounded F j).inv.app X).hom :=
  HomologicalComplex.singleMapHomologicalComplex_comp_inv_app F G (.up ℤ) j X

end CochainComplex.Bounded

end
