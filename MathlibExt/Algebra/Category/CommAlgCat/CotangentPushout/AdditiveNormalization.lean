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

public import MathlibExt.AlgebraicTopology.DoldKan.AdditiveNormalizationCoherence
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout.Chain

/-!
# Normalization and scalar change for higher cotangent forms

Let `k → K` be a morphism of commutative rings, `A` a commutative `k`-algebra, and
`S = K ⊗[k] A`. For an augmented simplicial algebra `P → const A`, scalar extension
identifies its degreewise weight-`n` higher-form diagram with that of `K ⊗[k] P` over `K`.

The additive normalization comparison gives a natural isomorphism from the scalar
extension of the normalized higher-form complex to the normalized scalar-changed
model. Its forward and inverse maps agree with the corresponding chain homotopy
comparison maps. This statement compares complexes; it does not interchange tensor
products and homology. The universes of `k`, `K`, and the algebra carriers are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite AlgebraicTopology
open scoped Simplicial TensorProduct

universe u v w uC vC uD vD

namespace CommAlgCat.CotangentPushout

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]
  (A : CommAlgCat.{max u v w} k)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem comparisonHomFormula
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (X : SimplicialObject C) (Y : SimplicialObject D)
    (ψ : X ⋙ F ≅ Y) :
    (((NormalizedQuotient.mooreCompMapIso F).app X) ≪≫ (normalizedMooreComplex D).mapIso ψ).hom =
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
        ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X ≪≫
          (alternatingFaceMapComplex D).mapIso ψ).hom ≫ DoldKan.PInftyToNormalizedMooreComplex Y := by
  rw [Iso.trans_hom, Functor.mapIso_hom, NormalizedQuotient.mooreCompMapIso_hom]
  have hp := (DoldKan.PInftyToNormalizedMooreComplex_naturality ψ.hom).symm
  change DoldKan.PInftyToNormalizedMooreComplex (X ⋙ F) ≫ (normalizedMooreComplex D).map ψ.hom =
    (alternatingFaceMapComplex D).map ψ.hom ≫ DoldKan.PInftyToNormalizedMooreComplex Y at hp
  change ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X ≫
        DoldKan.PInftyToNormalizedMooreComplex (X ⋙ F)) ≫ (normalizedMooreComplex D).map ψ.hom =
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X ≫
        (alternatingFaceMapComplex D).map ψ.hom) ≫ DoldKan.PInftyToNormalizedMooreComplex Y
  let j := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X)
  let a := (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X
  let p := DoldKan.PInftyToNormalizedMooreComplex (X ⋙ F)
  let f := (normalizedMooreComplex D).map ψ.hom
  let g := (alternatingFaceMapComplex D).map ψ.hom
  let q := DoldKan.PInftyToNormalizedMooreComplex Y
  exact (Category.assoc j (a ≫ p) f).trans
    ((congrArg (fun m => j ≫ m) (Category.assoc a p f)).trans
      ((congrArg (fun m => j ≫ a ≫ m) hp).trans
        (congrArg (fun m => j ≫ m) (Category.assoc a g q).symm)))

private theorem comparisonInvFormula
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (X : SimplicialObject C) (Y : SimplicialObject D)
    (ψ : X ⋙ F ≅ Y) :
    (((NormalizedQuotient.mooreCompMapIso F).app X) ≪≫ (normalizedMooreComplex D).mapIso ψ).inv =
      (inclusionOfMooreComplexMap Y ≫
        ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X ≪≫
          (alternatingFaceMapComplex D).mapIso ψ).inv) ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (DoldKan.PInftyToNormalizedMooreComplex X) := by
  rw [Iso.trans_inv, Functor.mapIso_inv, NormalizedQuotient.mooreCompMapIso_inv]
  have hi := (inclusionOfMooreComplex D).naturality ψ.inv
  change (normalizedMooreComplex D).map ψ.inv ≫ inclusionOfMooreComplexMap (X ⋙ F) =
    inclusionOfMooreComplexMap Y ≫ (alternatingFaceMapComplex D).map ψ.inv at hi
  change (normalizedMooreComplex D).map ψ.inv ≫
      inclusionOfMooreComplexMap (X ⋙ F) ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app X ≫
          (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (DoldKan.PInftyToNormalizedMooreComplex X) =
    (inclusionOfMooreComplexMap Y ≫
      ((alternatingFaceMapComplex D).map ψ.inv ≫
        (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app X)) ≫
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (DoldKan.PInftyToNormalizedMooreComplex X)
  simpa only [Category.assoc] using congrArg
    (fun m => m ≫ (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app X ≫
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (DoldKan.PInftyToNormalizedMooreComplex X)) hi

/--
For an augmented simplicial algebra `P → const A` and weight `n`, the natural
isomorphism from the scalar extension of its normalized higher-form complex to the
normalized higher-form complex of the scalar-changed augmented diagram.
-/
def normalizedPushoutIso (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    (mappedNormalizedFunctor.{u, v, w} k K A n).obj P ≅ (targetNormalizedFunctor.{u, v, w} k K A n).obj P :=
  ((NormalizedQuotient.mooreCompMapIso (moduleFunctor.{u, v, w} k K A)).app (higherSimplicial.{u, v, w} k A n P)) ≪≫
    normalizedDiagramIso.{u, v, w} k K A n P

/--
The forward map of `normalizedPushoutIso` equals the forward map of the higher-form
chain homotopy equivalence `normalizedHomotopyEquiv` on the same augmented diagram.
-/
theorem normalizedPushoutIso_hom_eq_old (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    (normalizedPushoutIso.{u, v, w} k K A n P).hom = (normalizedHomotopyEquiv.{u, v, w} k K A n P).hom := by
  let X := higherSimplicial.{u, v, w} k A n P
  let Y := higherSimplicial.{w, v, u} K (target.{u, v, w} k K A) n (resolution.{u, v, w} k K A P)
  let ψ := higherSimplicialIso.{u, v, w} k K A n P
  have h := comparisonHomFormula (moduleFunctor.{u, v, w} k K A) X Y ψ
  have old := normalizedHomotopyEquiv_hom.{u, v, w} k K A n P
  dsimp only [alternatingIso] at old
  simpa only [X, Y, ψ, normalizedPushoutIso, normalizedDiagramIso, mappedNormalizedFunctor,
    normalizedFunctor, targetNormalizedFunctor, higherSimplicialFunctor, resolutionFunctor,
    Functor.comp_obj, normalizedMooreComplex] using h.trans old.symm

/--
The inverse map of `normalizedPushoutIso` equals the inverse map of the higher-form
chain homotopy equivalence `normalizedHomotopyEquiv` on the same augmented diagram.
-/
theorem normalizedPushoutIso_inv_eq_old (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    (normalizedPushoutIso.{u, v, w} k K A n P).inv = (normalizedHomotopyEquiv.{u, v, w} k K A n P).inv := by
  let X := higherSimplicial.{u, v, w} k A n P
  let Y := higherSimplicial.{w, v, u} K (target.{u, v, w} k K A) n (resolution.{u, v, w} k K A P)
  let ψ := higherSimplicialIso.{u, v, w} k K A n P
  have h := comparisonInvFormula (moduleFunctor.{u, v, w} k K A) X Y ψ
  have old : (normalizedHomotopyEquiv.{u, v, w} k K A n P).inv =
      (inclusionOfMooreComplexMap Y ≫ (alternatingIso.{u, v, w} k K A n P).inv) ≫
        ((moduleFunctor.{u, v, w} k K A).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (DoldKan.PInftyToNormalizedMooreComplex X) := rfl
  dsimp only [alternatingIso] at old
  simpa only [X, Y, ψ, normalizedPushoutIso, normalizedDiagramIso, mappedNormalizedFunctor,
    normalizedFunctor, targetNormalizedFunctor, higherSimplicialFunctor, resolutionFunctor,
    Functor.comp_obj, normalizedMooreComplex] using h.trans old.symm

/--
The natural isomorphism between scalar extension after higher-form normalization and
higher-form normalization of the scalar-changed augmented diagram, at weight `n`.
-/
def normalizedPushoutNatIso (n : ℕ) :
    mappedNormalizedFunctor.{u, v, w} k K A n ≅ targetNormalizedFunctor.{u, v, w} k K A n :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (higherSimplicialFunctor.{u, v, w} k A n)
      (NormalizedQuotient.mooreCompMapIso (moduleFunctor.{u, v, w} k K A)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (higherSimplicialNatIso.{u, v, w} k K A n)
      (normalizedMooreComplex (ModuleCat.{max u v w} (target.{u, v, w} k K A))) ≪≫
    Functor.associator _ _ _

/--
The component of `normalizedPushoutNatIso` at an augmented simplicial algebra `P` is
`normalizedPushoutIso` for that same weight and diagram.
-/
@[simp]
theorem normalizedPushoutNatIso_app (n : ℕ)
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    (normalizedPushoutNatIso.{u, v, w} k K A n).app P = normalizedPushoutIso.{u, v, w} k K A n P := by
  apply Iso.ext
  simp only [Iso.app_hom, normalizedPushoutNatIso, normalizedPushoutIso, normalizedDiagramIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Functor.mapIso_hom, Category.id_comp, Category.comp_id] <;> rfl

/--
For an augmented-algebra map `f : P ⟶ Q`, the normalized higher-form comparison
commutes with the induced maps on the scalar-extended and scalar-changed complexes:
`mapped.map f ≫ comparison_Q = comparison_P ≫ target.map f`.
-/
@[reassoc]
theorem normalizedPushoutIso_naturality (n : ℕ)
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)} (f : P ⟶ Q) :
    (mappedNormalizedFunctor.{u, v, w} k K A n).map f ≫ (normalizedPushoutIso.{u, v, w} k K A n Q).hom =
      (normalizedPushoutIso.{u, v, w} k K A n P).hom ≫ (targetNormalizedFunctor.{u, v, w} k K A n).map f := by
  have h := (normalizedPushoutNatIso.{u, v, w} k K A n).hom.naturality f
  change (mappedNormalizedFunctor.{u, v, w} k K A n).map f ≫
      ((normalizedPushoutNatIso.{u, v, w} k K A n).app Q).hom =
    ((normalizedPushoutNatIso.{u, v, w} k K A n).app P).hom ≫
      (targetNormalizedFunctor.{u, v, w} k K A n).map f at h
  simpa only [normalizedPushoutNatIso_app] using h

end CommAlgCat.CotangentPushout
