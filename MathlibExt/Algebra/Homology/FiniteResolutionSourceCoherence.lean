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
# Coherence of source and target changes for finite resolutions

Changing the resolving category of a finite resolution is compatible with identity functors and
composition. The comparison chain maps have identity components and commute with the transported
augmentations. An additive source change also commutes with an additive, homology-preserving
change of abelian target, after using the natural isomorphisms relating the resolving functors.
Both orders give the same resolving complex, augmentation and inclusive support bound.
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

/-- Let P be preadditive, A abelian, and i : P → A additive. For a finite resolution R of X relative
to i, mapSourceIdentityMap is the canonical chain map from the resolution obtained by the
identity source change, with compatibility i ∘ id_P ≅ i, to R.complex. -/
def mapSourceIdentityMap (R : FiniteResolution i X) :
    (R.mapSource (𝟭 P) (Functor.leftUnitor i)).complex ⟶ R.complex :=
  (Functor.mapHomologicalComplexIdIso P (ComplexShape.down ℕ)).hom.app R.complex

/-- Let P be preadditive, A abelian, i : P → A additive, and R a finite resolution of X. For every
natural number n, the degree-n component of mapSourceIdentityMap R is the identity of Rₙ. -/
theorem mapSourceIdentityMap_f (R : FiniteResolution i X) (n : ℕ) :
    (mapSourceIdentityMap R).f n = 𝟙 (R.complex.X n) :=
  rfl

/-- Let P be preadditive, A abelian, i : P → A additive, and R a finite resolution of X. If c is
mapSourceIdentityMap R and ε_id is the identity-source-changed augmentation, then i(c) ≫ ε_R =
ε_id as chain maps to X[0]. -/
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

/-- Let P, Q, S and A be categories, with functors i : P → A, j : Q → A, k : S → A, F : P → Q and G
: Q → S. Natural isomorphisms e_F : jF ≅ i and e_G : kG ≅ j determine the natural isomorphism
kGF ≅ i, using associativity of composition and the components of e_G followed by e_F. -/
def sourceCompCompatibility : (F ⋙ G) ⋙ k ≅ i :=
  Functor.associator F G k ≪≫ Functor.isoWhiskerLeft F eG ≪≫ eF

omit [Preadditive P] [Abelian A] [Preadditive Q] [Preadditive S]
  [i.Additive] [j.Additive] [k.Additive] [F.Additive] [G.Additive] in
/-- Let i : P → A, j : Q → A, k : S → A, F : P → Q and G : Q → S be functors between categories,
with e_F : jF ≅ i and e_G : kG ≅ j. At Y ∈ P, the forward component of sourceCompCompatibility
is e_G,F(Y) ≫ e_F,Y : k(G(F(Y))) → i(Y). -/
theorem sourceCompCompatibility_hom_app (Y : P) :
    (sourceCompCompatibility F G eF eG).hom.app Y = eG.hom.app (F.obj Y) ≫ eF.hom.app Y := by
  unfold sourceCompCompatibility
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp]

/-- Let P, Q and S be preadditive, A abelian, and i : P → A, j : Q → A, k : S → A additive. Given
additive F : P → Q and G : Q → S with e_F : jF ≅ i and e_G : kG ≅ j, and a finite resolution R
of X relative to i, mapSourceCompMap compares the resolving complex obtained by first F and then
G with that obtained by GF using sourceCompCompatibility. It is the canonical comparison G(F(R))
→ (GF)(R). -/
def mapSourceCompMap (R : FiniteResolution i X) :
    ((R.mapSource F eF).mapSource G eG).complex ⟶
      (R.mapSource (F ⋙ G) (sourceCompCompatibility F G eF eG)).complex :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
    (ComplexShape.down ℕ)).hom.app R.complex

/-- Let P, Q and S be preadditive, A abelian, and i : P → A, j : Q → A, k : S → A additive. Given
additive F : P → Q and G : Q → S with e_F : jF ≅ i and e_G : kG ≅ j, and a finite resolution R
of X relative to i, the degree-n component of mapSourceCompMap is the identity of G(F(Rₙ)), for
every natural number n. -/
theorem mapSourceCompMap_f (R : FiniteResolution i X) (n : ℕ) :
    (mapSourceCompMap F G eF eG R).f n = 𝟙 (G.obj (F.obj (R.complex.X n))) :=
  rfl

/-- Let P, Q and S be preadditive, A abelian, and i : P → A, j : Q → A, k : S → A additive. Given
additive F : P → Q and G : Q → S with e_F : jF ≅ i and e_G : kG ≅ j, and a finite resolution R
of X relative to i, let c : G(F(R)) → (GF)(R) be mapSourceCompMap, and let ε_two and ε_comp be
the iterated and composite source-change augmentations. Then k(c) ≫ ε_comp = ε_two as chain maps
to X[0]. -/
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

/-- Let P, Q and S be preadditive, A abelian, and i : P → A, j : Q → A, k : S → A additive. Given
additive F : P → Q and G : Q → S with e_F : jF ≅ i and e_G : kG ≅ j, and a finite resolution R
of X relative to i, the support bounds of the two-step source change and the source change along
GF with sourceCompCompatibility are equal. Both equal R.bound. -/
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

/-- Let P, Q, A and B be categories, with functors i : P → A, j : Q → A, k : Q → B, F : P → Q and H
: A → B. Natural isomorphisms e_F : jF ≅ i and e_H : Hj ≅ k give sourceTargetCompatibility : Hi
≅ kF. Its forward map applies H to e_F⁻¹ and then uses e_H at F(Y). -/
def sourceTargetCompatibility : i ⋙ H ≅ F ⋙ k :=
  (Functor.isoWhiskerRight eF H).symm ≪≫ Functor.associator F j H ≪≫
    Functor.isoWhiskerLeft F eH

omit [Preadditive P] [Abelian A] [i.Additive] [Preadditive Q] [Abelian B]
  [j.Additive] [k.Additive] [F.Additive] [H.Additive] [H.PreservesHomology] in
/-- Let i : P → A, j : Q → A, k : Q → B, F : P → Q and H : A → B be functors between categories,
with e_F : jF ≅ i and e_H : Hj ≅ k. At Y ∈ P, the inverse component of sourceTargetCompatibility
is e_H,F(Y)⁻¹ ≫ H(e_F,Y) : k(F(Y)) → H(i(Y)). -/
theorem sourceTargetCompatibility_inv_app (Y : P) :
    (sourceTargetCompatibility F H eF eH).inv.app Y =
      eH.inv.app (F.obj Y) ≫ H.map (eF.hom.app Y) := by
  change (eH.inv.app (F.obj Y) ≫ 𝟙 _) ≫ H.map (eF.hom.app Y) = _
  simp only [Category.comp_id]

/-- Let P and Q be preadditive, A and B abelian, and i : P → A, j : Q → A, k : Q → B additive. Let F
: P → Q be additive and H : A → B additive and homology preserving, with e_F : jF ≅ i and e_H :
Hj ≅ k. For a finite resolution R of X relative to i, source change along F followed by target
change along H has the same resolving complex as target change using sourceTargetCompatibility
followed by source change along F with the identity compatibility. Both complexes are F(R). -/
theorem mapSourceTarget_complex (R : FiniteResolution i X) :
    ((R.mapSource F eF).mapTarget H eH).complex =
      ((R.mapTarget H (sourceTargetCompatibility F H eF eH)).mapSource F
        (Iso.refl (F ⋙ k))).complex :=
  rfl

/-- Let P and Q be preadditive, A and B abelian, and i : P → A, j : Q → A, k : Q → B additive. Let F
: P → Q be additive and H : A → B additive and homology preserving, with e_F : jF ≅ i and e_H :
Hj ≅ k. For a finite resolution R of X relative to i, the augmentation of the
source-then-target-changed resolution equals the augmentation of the target-then-source-changed
resolution, using sourceTargetCompatibility for the target-first step and the identity
compatibility for the source step. Both maps have source kF(R) and target H(X)[0]. -/
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

/-- Let P and Q be preadditive, A and B abelian, and i : P → A, j : Q → A, k : Q → B additive. Let F
: P → Q be additive and H : A → B additive and homology preserving, with e_F : jF ≅ i and e_H :
Hj ≅ k. For a finite resolution R of X relative to i, the two orders of source and target change
have equal inclusive support bounds, each equal to R.bound. -/
theorem mapSourceTarget_bound (R : FiniteResolution i X) :
    ((R.mapSource F eF).mapTarget H eH).bound =
      ((R.mapTarget H (sourceTargetCompatibility F H eF eH)).mapSource F
        (Iso.refl (F ⋙ k))).bound :=
  rfl

end Interchange

end CategoryTheory.Abelian.FiniteResolution

end
