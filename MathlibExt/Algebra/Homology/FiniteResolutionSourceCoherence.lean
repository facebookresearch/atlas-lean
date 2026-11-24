/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FiniteResolutionSourceChange
public import MathlibExt.Algebra.Homology.FiniteResolutionTargetChange
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Whiskering

/-!
# Original source-change resolution maps and augmentation coherence

Identity and composition use the canonical maps of the image complexes. Their component maps are
original identities, and their augmentation equations retain the original compatibility
isomorphisms. Source/target interchange keeps the same resolving complex and identifies the
complete augmentation programs through original naturality. All support bounds remain the original
bounds.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uP vP uQ vQ uS vS uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {i : P ⥤ A} [i.Additive] {X : A}

/-- The canonical identity-source comparison map on the original resolving complex. -/
def mapSourceIdentityMap (R : FiniteResolution i X) :
    (R.mapSource (𝟭 P) (Functor.leftUnitor i)).complex ⟶ R.complex :=
  (Functor.mapHomologicalComplexIdIso P (ComplexShape.down ℕ)).hom.app R.complex

/-- Every component of the identity-source comparison is the original identity. -/
theorem mapSourceIdentityMap_f (R : FiniteResolution i X) (n : ℕ) :
    (mapSourceIdentityMap R).f n = 𝟙 (R.complex.X n) :=
  rfl

/-- The original identity-source map respects the augmentation. -/
theorem mapSourceIdentityMap_augmentation (R : FiniteResolution i X) :
    (i.mapHomologicalComplex (ComplexShape.down ℕ)).map (mapSourceIdentityMap R) ≫
        R.augmentation =
      (R.mapSource (𝟭 P) (Functor.leftUnitor i)).augmentation := by
  apply HomologicalComplex.hom_ext
  intro n
  change i.map (𝟙 (R.complex.X n)) ≫ R.augmentation.f n =
    𝟙 (i.obj (R.complex.X n)) ≫ R.augmentation.f n
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

section Composition

variable {Q : Type uQ} [Category.{vQ} Q] [Preadditive Q]
variable {S : Type uS} [Category.{vS} S] [Preadditive S]
variable {j : Q ⥤ A} [j.Additive] {k : S ⥤ A} [k.Additive]
variable (F : P ⥤ Q) [F.Additive] (G : Q ⥤ S) [G.Additive]
variable (eF : F ⋙ j ≅ i) (eG : G ⋙ k ≅ j)

/--
The composite resolving-functor compatibility, built from the original associator and original two
compatibility isomorphisms.
-/
def sourceCompCompatibility : (F ⋙ G) ⋙ k ≅ i :=
  Functor.associator F G k ≪≫ Functor.isoWhiskerLeft F eG ≪≫ eF

omit [Preadditive P] [Abelian A] [Preadditive Q] [Preadditive S]
  [i.Additive] [j.Additive] [k.Additive] [F.Additive] [G.Additive] in
/-- The original composite compatibility component is the original
second component followed by the original first component. -/
theorem sourceCompCompatibility_hom_app (Y : P) :
    (sourceCompCompatibility F G eF eG).hom.app Y = eG.hom.app (F.obj Y) ≫ eF.hom.app Y := by
  unfold sourceCompCompatibility
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp]

/--
Compare the two-step and one-step image complexes using the original canonical homological-complex
composition map.
-/
def mapSourceCompMap (R : FiniteResolution i X) :
    ((R.mapSource F eF).mapSource G eG).complex ⟶
      (R.mapSource (F ⋙ G) (sourceCompCompatibility F G eF eG)).complex :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
    (ComplexShape.down ℕ)).hom.app R.complex

/-- Every original source-composition map component is the identity on the twice-mapped original term. -/
theorem mapSourceCompMap_f (R : FiniteResolution i X) (n : ℕ) :
    (mapSourceCompMap F G eF eG R).f n = 𝟙 (G.obj (F.obj (R.complex.X n))) :=
  rfl

/--
The canonical source-composition map respects the complete original augmentation program, with the
original compatibility components.
-/
theorem mapSourceCompMap_augmentation (R : FiniteResolution i X) :
    (k.mapHomologicalComplex (ComplexShape.down ℕ)).map (mapSourceCompMap F G eF eG R) ≫
        (R.mapSource (F ⋙ G) (sourceCompCompatibility F G eF eG)).augmentation =
      ((R.mapSource F eF).mapSource G eG).augmentation := by
  apply HomologicalComplex.hom_ext
  intro n
  change k.map (𝟙 (G.obj (F.obj (R.complex.X n)))) ≫
      ((sourceCompCompatibility F G eF eG).hom.app (R.complex.X n) ≫ R.augmentation.f n) =
    eG.hom.app (F.obj (R.complex.X n)) ≫ (eF.hom.app (R.complex.X n) ≫ R.augmentation.f n)
  rw [CategoryTheory.Functor.map_id, Category.id_comp, sourceCompCompatibility_hom_app]
  exact Category.assoc _ _ _

/-- Both source-composition resolution records retain the exact original support bound. -/
theorem mapSourceComp_bound (R : FiniteResolution i X) :
    ((R.mapSource F eF).mapSource G eG).bound =
      (R.mapSource (F ⋙ G) (sourceCompCompatibility F G eF eG)).bound :=
  rfl

end Composition

section Interchange

variable {Q : Type uQ} [Category.{vQ} Q] [Preadditive Q]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {j : Q ⥤ A} [j.Additive] {k : Q ⥤ B} [k.Additive]
variable (F : P ⥤ Q) [F.Additive] (H : A ⥤ B) [H.Additive] [H.PreservesHomology]
variable (eF : F ⋙ j ≅ i) (eH : j ⋙ H ≅ k)

/-- The original source/target compatibility, with the original inverse
first comparison and the original target comparison components. -/
def sourceTargetCompatibility : i ⋙ H ≅ F ⋙ k :=
  (Functor.isoWhiskerRight eF H).symm ≪≫ Functor.associator F j H ≪≫
    Functor.isoWhiskerLeft F eH

omit [Preadditive P] [Abelian A] [i.Additive] [Preadditive Q] [Abelian B]
  [j.Additive] [k.Additive] [F.Additive] [H.Additive] [H.PreservesHomology] in
/--
The inverse interchange component is the original target inverse component followed by the mapped
original source component.
-/
theorem sourceTargetCompatibility_inv_app (Y : P) :
    (sourceTargetCompatibility F H eF eH).inv.app Y =
      eH.inv.app (F.obj Y) ≫ H.map (eF.hom.app Y) := by
  change (eH.inv.app (F.obj Y) ≫ 𝟙 _) ≫ H.map (eF.hom.app Y) = _
  simp only [Category.comp_id]

/--
Source-first and target-first change have the same image complex, with the original source functor
applied to the original complex.
-/
theorem mapSourceTarget_complex (R : FiniteResolution i X) :
    ((R.mapSource F eF).mapTarget H eH).complex =
      ((R.mapTarget H (sourceTargetCompatibility F H eF eH)).mapSource F
        (Iso.refl (F ⋙ k))).complex :=
  rfl

/-- Source/target interchange identifies the full original augmentation
programs, with the original mapped augmentation and canonical single comparison. -/
theorem mapSourceTarget_augmentation (R : FiniteResolution i X) :
    ((R.mapSource F eF).mapTarget H eH).augmentation =
      ((R.mapTarget H (sourceTargetCompatibility F H eF eH)).mapSource F
        (Iso.refl (F ⋙ k))).augmentation := by
  apply HomologicalComplex.hom_ext
  intro n
  change eH.inv.app (F.obj (R.complex.X n)) ≫
      H.map (eF.hom.app (R.complex.X n) ≫ R.augmentation.f n) ≫
        ((HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.down ℕ) 0).hom.app X).f n =
    𝟙 _ ≫ ((sourceTargetCompatibility F H eF eH).inv.app (R.complex.X n) ≫
      H.map (R.augmentation.f n) ≫
        ((HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.down ℕ) 0).hom.app X).f n)
  rw [Category.id_comp, sourceTargetCompatibility_inv_app, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

/-- Interchange retains the same exact original support bound in both orders. -/
theorem mapSourceTarget_bound (R : FiniteResolution i X) :
    ((R.mapSource F eF).mapTarget H eH).bound =
      ((R.mapTarget H (sourceTargetCompatibility F H eF eH)).mapSource F
        (Iso.refl (F ⋙ k))).bound :=
  rfl

end Interchange

end CategoryTheory.Abelian.FiniteResolution

end
