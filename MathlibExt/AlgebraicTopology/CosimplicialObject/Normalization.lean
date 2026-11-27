/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.Algebra.Homology.Opposite
public import MathlibExt.Algebra.Homology.Embedding.RestrictionHomology
public import MathlibExt.CategoryTheory.Preadditive.SplitKernel
public import MathlibExt.Algebra.Homology.Opposite.MapFunctor
public import MathlibExt.Algebra.Homology.Embedding.MapRestriction
public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedQuotient.MapFunctor

/-!
# Normalization of cosimplicial objects

Duality transports the normalized Moore construction to cosimplicial objects.
The associated normalized cochain functor has natural projection and inclusion
maps, with comparison laws for coefficient functors. In an abelian category
these maps are quasi-isomorphisms, and the inclusion gives the comparison on
cohomology. The constructions retain independent category universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped Simplicial

universe v u

namespace AlgebraicTopology

variable (A : Type u) [Category.{v} A]

local notation "E" => Equivalence.functor (cosimplicialSimplicialEquiv A)

/-- The identity-on-degrees embedding from the cochain shape to the opposite chain shape. -/
def upEmbeddingDownSymm : (ComplexShape.up ℕ).Embedding (ComplexShape.down ℕ).symm :=
  .mk' _ _ id Function.injective_id (fun _ _ ↦ Iff.rfl)

instance : upEmbeddingDownSymm.IsRelIff := by
  constructor
  intro _ _ h
  exact h

/-- Native unop followed by restriction along the identity shape embedding, with codomain exactly
the usual cochain-complex category. -/
def chainComplexUnopFunctor [Preadditive A] :
    (ChainComplex Aᵒᵖ ℕ)ᵒᵖ ⥤ CochainComplex A ℕ :=
  HomologicalComplex.unopFunctor A (ComplexShape.down ℕ) ⋙
    upEmbeddingDownSymm.restrictionFunctor A

local notation "U" => chainComplexUnopFunctor A

section WhiskeringOpposite

universe uD vD

variable {D : Type uD} [Category.{vD} D] (F : A ⥤ D)

/-- Opposite simplicial objects retain the given cosimplicial coefficient functor. -/
def cosimplicialSimplicialWhiskeringIso :
    (cosimplicialSimplicialEquiv A).functor ⋙
        ((SimplicialObject.whiskering Aᵒᵖ Dᵒᵖ).obj F.op) ≅
      ((CosimplicialObject.whiskering A D).obj F).op ⋙
        (cosimplicialSimplicialEquiv D).functor :=
  NatIso.ofComponents (fun X => (Functor.opComp X.unop F).symm) (by
    intro X Y f
    apply NatTrans.ext
    funext n
    change (F.map (f.unop.app n.unop)).op ≫ 𝟙 _ =
      𝟙 _ ≫ (F.map (f.unop.app n.unop)).op
    rw [Category.comp_id, Category.id_comp])

end WhiskeringOpposite

section Preadditive

variable [Preadditive A]

/-- Exact-shape unop is additive by the unop and restriction functors. -/
instance chainComplexUnopFunctor_additive : (chainComplexUnopFunctor A).Additive := by
  dsimp only [chainComplexUnopFunctor]
  infer_instance

/-- Components of the exact-shape unop functor are the unopped components. -/
@[simp]
theorem chainComplexUnopFunctor_map_f {K L : ChainComplex Aᵒᵖ ℕ}
    (f : K ⟶ L) (n : ℕ) :
    ((chainComplexUnopFunctor A).map f.op).f n = (f.f n).unop := by
  rfl

/-- Objectwise form of the duality comparison for the alternating coface complex. -/
def alternatingCofaceUnopObjIso (X : CosimplicialObject A) :
    (alternatingCofaceMapComplex A).obj X ≅
      (((E ⋙ alternatingFaceMapComplex Aᵒᵖ).rightOp ⋙ U).obj X) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    change 𝟙 _ ≫ (((alternatingFaceMapComplex Aᵒᵖ).obj ((E).obj (op X))).d
        (i + 1) i).unop =
      ((alternatingCofaceMapComplex A).obj X).d i (i + 1) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    dsimp only [alternatingCofaceMapComplex, alternatingFaceMapComplex,
      AlternatingCofaceMapComplex.obj, AlternatingFaceMapComplex.obj]
    rw [CochainComplex.of_d, ChainComplex.of_d]
    exact (AlternatingCofaceMapComplex.d_eq_unop_d X i).symm)

/-- The alternating coface complex is the dual alternating face complex. -/
def alternatingCofaceUnopIso : alternatingCofaceMapComplex A ≅
    (E ⋙ alternatingFaceMapComplex Aᵒᵖ).rightOp ⋙ U :=
  NatIso.ofComponents (alternatingCofaceUnopObjIso A) (fun {X Y} f ↦ by
    ext n
    dsimp [alternatingCofaceUnopObjIso, chainComplexUnopFunctor,
      ComplexShape.Embedding.restrictionFunctor,
      HomologicalComplex.restrictionMap, upEmbeddingDownSymm]
    change f.app ⦋n⦌ ≫ 𝟙 _ = 𝟙 _ ≫ (f.app ⦋n⦌).op.unop
    simp)

/-- Its forward comparison has identity degree maps. -/
theorem alternatingCofaceUnopIso_hom_f (X : CosimplicialObject A) (n : ℕ) :
    ((alternatingCofaceUnopIso A).hom.app X).f n = 𝟙 _ := by
  change (Iso.refl _).hom = 𝟙 _
  rfl

/-- Its inverse comparison has identity degree maps. -/
theorem alternatingCofaceUnopIso_inv_f (X : CosimplicialObject A) (n : ℕ) :
    ((alternatingCofaceUnopIso A).inv.app X).f n = 𝟙 _ := by
  change (Iso.refl _).inv = 𝟙 _
  rfl

section MapFunctor

universe uD vD

variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  (F : A ⥤ D) [F.Additive]

/-- The given exact-shape unop commutes with any additive coefficient functor. -/
def chainComplexUnopFunctorCompMapIso :
    chainComplexUnopFunctor A ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ) ≅
      ((F.op).mapHomologicalComplex (ComplexShape.down ℕ)).op ⋙ chainComplexUnopFunctor D :=
  Functor.associator
      (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ))
      (upEmbeddingDownSymm.restrictionFunctor A)
      (F.mapHomologicalComplex (ComplexShape.up ℕ)) ≪≫
    isoWhiskerLeft (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ))
      (HomologicalComplex.restrictionFunctorCompMapIso upEmbeddingDownSymm F) ≪≫
    (Functor.associator (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ))
      (F.mapHomologicalComplex (ComplexShape.down ℕ).symm)
      (upEmbeddingDownSymm.restrictionFunctor D)).symm ≪≫
    isoWhiskerRight
      (HomologicalComplex.unopFunctorCompMapIso F (ComplexShape.down ℕ))
      (upEmbeddingDownSymm.restrictionFunctor D) ≪≫
    Functor.associator
      ((F.op).mapHomologicalComplex (ComplexShape.down ℕ)).op
      (HomologicalComplex.unopFunctor D (ComplexShape.down ℕ))
      (upEmbeddingDownSymm.restrictionFunctor D)

/-- The coefficient comparison uses the given identity maps after exact-shape unop. -/
@[simp]
theorem chainComplexUnopFunctorCompMapIso_hom_app_f
    (K : (ChainComplex Aᵒᵖ ℕ)ᵒᵖ) (n : ℕ) :
    ((chainComplexUnopFunctorCompMapIso A F).hom.app K).f n = 𝟙 _ := by
  dsimp only [chainComplexUnopFunctorCompMapIso, Iso.trans_hom,
    NatTrans.comp_app, HomologicalComplex.comp_f]
  change (𝟙 (F.obj (K.unop.X n).unop) ≫
    𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) = 𝟙 _
  simp only [Category.id_comp]

/-- The given alternating coface functor commutes with an additive coefficient functor. -/
def alternatingCofaceCompMapIso :
    alternatingCofaceMapComplex A ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ) ≅
      ((CosimplicialObject.whiskering A D).obj F) ⋙ alternatingCofaceMapComplex D := by
  let EC := (cosimplicialSimplicialEquiv A).functor
  let ED := (cosimplicialSimplicialEquiv D).functor
  let S := (SimplicialObject.whiskering Aᵒᵖ Dᵒᵖ).obj F.op
  let T := (CosimplicialObject.whiskering A D).obj F
  let H := (F.op).mapHomologicalComplex (ComplexShape.down ℕ)
  let NC := alternatingFaceMapComplex Aᵒᵖ
  let ND := alternatingFaceMapComplex Dᵒᵖ
  let e : (EC ⋙ NC) ⋙ H ≅ T.op ⋙ (ED ⋙ ND) :=
    Functor.associator EC NC H ≪≫
      isoWhiskerLeft EC (alternatingFaceMapComplexCompMapHomologicalComplexIso F.op) ≪≫
      (Functor.associator EC S ND).symm ≪≫
      isoWhiskerRight (cosimplicialSimplicialWhiskeringIso A F) ND ≪≫
      Functor.associator T.op ED ND
  let e' := Functor.associator (EC ⋙ NC).rightOp (chainComplexUnopFunctor A)
      (F.mapHomologicalComplex (ComplexShape.up ℕ)) ≪≫
    isoWhiskerLeft (EC ⋙ NC).rightOp (chainComplexUnopFunctorCompMapIso A F) ≪≫
    (Functor.associator (EC ⋙ NC).rightOp H.op (chainComplexUnopFunctor D)).symm ≪≫
    isoWhiskerRight (Functor.rightOpComp (EC ⋙ NC) H).symm (chainComplexUnopFunctor D) ≪≫
    isoWhiskerRight (NatIso.rightOp e.symm) (chainComplexUnopFunctor D) ≪≫
    isoWhiskerRight (Functor.rightOpCompOp T (ED ⋙ ND)) (chainComplexUnopFunctor D) ≪≫
    Functor.associator T (ED ⋙ ND).rightOp (chainComplexUnopFunctor D)
  exact isoWhiskerRight (alternatingCofaceUnopIso A)
      (F.mapHomologicalComplex (ComplexShape.up ℕ)) ≪≫ e' ≪≫
    isoWhiskerLeft T (alternatingCofaceUnopIso D).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The alternating-coface comparison retains the given coefficient object in every degree. -/
@[simp]
theorem alternatingCofaceCompMapIso_hom_app_f (X : CosimplicialObject A) (n : ℕ) :
    ((alternatingCofaceCompMapIso A F).hom.app X).f n = 𝟙 _ := by
  let EC := (cosimplicialSimplicialEquiv A).functor
  let ED := (cosimplicialSimplicialEquiv D).functor
  let S := (SimplicialObject.whiskering Aᵒᵖ Dᵒᵖ).obj F.op
  let T := (CosimplicialObject.whiskering A D).obj F
  let H := (F.op).mapHomologicalComplex (ComplexShape.down ℕ)
  let NC := alternatingFaceMapComplex Aᵒᵖ
  let ND := alternatingFaceMapComplex Dᵒᵖ
  let e : (EC ⋙ NC) ⋙ H ≅ T.op ⋙ (ED ⋙ ND) :=
    Functor.associator EC NC H ≪≫
      isoWhiskerLeft EC (alternatingFaceMapComplexCompMapHomologicalComplexIso F.op) ≪≫
      (Functor.associator EC S ND).symm ≪≫
      isoWhiskerRight (cosimplicialSimplicialWhiskeringIso A F) ND ≪≫
      Functor.associator T.op ED ND
  let W := S.obj (EC.obj (op X))
  let V := H.obj (NC.obj (EC.obj (op X)))
  let t : W ⟶ W := (cosimplicialSimplicialWhiskeringIso A F).inv.app (op X)
  have ht : t = 𝟙 W := rfl
  have hNt : ND.map t = 𝟙 (ND.obj W) :=
    (congrArg (fun f : W ⟶ W => ND.map f) ht).trans (ND.map_id W)
  let k : ND.obj W ⟶ V :=
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F.op).inv.app (EC.obj (op X))
  have he : (e.inv.app (op X)).f n =
      𝟙 (F.op.obj ((NC.obj (EC.obj (op X))).X n)) := by
    change ((((𝟙 (ND.obj W) ≫ ND.map t) ≫ 𝟙 (ND.obj W)) ≫ k) ≫ 𝟙 V).f n = _
    rw [hNt]
    simpa only [Category.id_comp, Category.comp_id] using
      (show k.f n = 𝟙 (F.op.obj ((NC.obj (EC.obj (op X))).X n)) from rfl)
  let Z := F.obj (X.obj ⦋n⦌)
  let α : Z ⟶ Z := F.map (((alternatingCofaceUnopIso A).hom.app X).f n)
  let κ : Z ⟶ Z := ((chainComplexUnopFunctorCompMapIso A F).hom.app
    (op (NC.obj (EC.obj (op X))))).f n
  let ν : Z ⟶ Z := ((e.inv.app (op X)).f n).unop
  let β : Z ⟶ Z := ((alternatingCofaceUnopIso D).inv.app (T.obj X)).f n
  have hα : α = 𝟙 Z := by
    change F.map (𝟙 (X.obj ⦋n⦌)) = 𝟙 Z
    exact F.map_id (X.obj ⦋n⦌)
  have hκ : κ = 𝟙 Z :=
    chainComplexUnopFunctorCompMapIso_hom_app_f A F (op (NC.obj (EC.obj (op X)))) n
  have hν : ν = 𝟙 Z :=
    congrArg (fun f : op Z ⟶ op Z => f.unop)
      (show ((e.inv.app (op X)).f n : op Z ⟶ op Z) = 𝟙 (op Z) from he)
  have hβ : β = 𝟙 Z := rfl
  change α ≫ ((𝟙 Z ≫ κ ≫ 𝟙 Z ≫ 𝟙 Z ≫ ν ≫ 𝟙 Z ≫ 𝟙 Z) ≫ β) = 𝟙 Z
  rw [hα, hκ, hν, hβ]
  simp only [Category.id_comp]

end MapFunctor

end Preadditive

section Abelian

variable [Abelian A]

/-- The exact-shape unop functor preserves quasi-isomorphisms. -/
lemma chainComplexUnopFunctor_map_quasiIso {K L : ChainComplex Aᵒᵖ ℕ}
    (f : K ⟶ L) [QuasiIso f] : QuasiIso ((chainComplexUnopFunctor A).map f.op) := by
  change QuasiIso (HomologicalComplex.restrictionMap
    ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map f.op)
      upEmbeddingDownSymm)
  rw [_root_.quasiIso_iff]
  intro i
  apply (HomologicalComplex.quasiIsoAt_restrictionMap_iff
    ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map f.op)
      upEmbeddingDownSymm i (by rfl) (by rfl)).2
  infer_instance

/-- Cosimplicial normalization uses the Moore functor in A.op. -/
def normalizedCofaceMapComplex : CosimplicialObject A ⥤ CochainComplex A ℕ :=
  (E ⋙ normalizedMooreComplex Aᵒᵖ).rightOp ⋙ U

/-- The chain inclusion becomes the natural cochain projection. -/
def normalizedCofaceMapProjection :
    alternatingCofaceMapComplex A ⟶ normalizedCofaceMapComplex A :=
  (alternatingCofaceUnopIso A).hom ≫
    Functor.whiskerRight
      (NatTrans.rightOp (Functor.whiskerLeft E (inclusionOfMooreComplex Aᵒᵖ))) U

/-- The chain projection becomes the natural normalized cochain inclusion. -/
def inclusionOfNormalizedCofaceMapComplex :
    normalizedCofaceMapComplex A ⟶ alternatingCofaceMapComplex A :=
  let ρ : alternatingFaceMapComplex Aᵒᵖ ⟶ normalizedMooreComplex Aᵒᵖ :=
    { app := DoldKan.PInftyToNormalizedMooreComplex
      naturality := fun {_ _} f ↦ DoldKan.PInftyToNormalizedMooreComplex_naturality f }
  Functor.whiskerRight (NatTrans.rightOp (Functor.whiskerLeft E ρ)) U ≫
    (alternatingCofaceUnopIso A).inv

/-- The cochain projection is the unop of the given Moore inclusion. -/
theorem normalizedCofaceMapProjection_app_f (X : CosimplicialObject A) (n : ℕ) :
    ((normalizedCofaceMapProjection A).app X).f n =
      ((inclusionOfMooreComplexMap
        ((cosimplicialSimplicialEquiv A).functor.obj (op X))).f n).unop := by
  change 𝟙 (unop (((alternatingFaceMapComplex Aᵒᵖ).obj
      ((cosimplicialSimplicialEquiv A).functor.obj (op X))).X n)) ≫
    ((inclusionOfMooreComplexMap
      ((cosimplicialSimplicialEquiv A).functor.obj (op X))).f n).unop = _
  exact Category.id_comp _

/-- The cochain inclusion is the unop of the given Moore projection. -/
theorem inclusionOfNormalizedCofaceMapComplex_app_f (X : CosimplicialObject A) (n : ℕ) :
    ((inclusionOfNormalizedCofaceMapComplex A).app X).f n =
      ((DoldKan.PInftyToNormalizedMooreComplex
        ((cosimplicialSimplicialEquiv A).functor.obj (op X))).f n).unop := by
  change ((DoldKan.PInftyToNormalizedMooreComplex
      ((cosimplicialSimplicialEquiv A).functor.obj (op X))).f n).unop ≫
    𝟙 (unop (((alternatingFaceMapComplex Aᵒᵖ).obj
      ((cosimplicialSimplicialEquiv A).functor.obj (op X))).X n)) = _
  exact Category.comp_id _

/-- The two maps split the normalized cochain functor. -/
theorem inclusionOfNormalizedCofaceMapComplex_comp_projection :
    inclusionOfNormalizedCofaceMapComplex A ≫ normalizedCofaceMapProjection A =
      𝟙 (normalizedCofaceMapComplex A) := by
  let ρ : alternatingFaceMapComplex Aᵒᵖ ⟶ normalizedMooreComplex Aᵒᵖ :=
    { app := DoldKan.PInftyToNormalizedMooreComplex
      naturality := fun {_ _} f ↦ DoldKan.PInftyToNormalizedMooreComplex_naturality f }
  have hρ : inclusionOfMooreComplex Aᵒᵖ ≫ ρ = 𝟙 _ := by
    ext S i
    exact congrArg (fun f ↦ (f.f i).unop)
      (DoldKan.splitMonoInclusionOfMooreComplexMap S).id
  have hU := congrArg (fun τ ↦
    Functor.whiskerRight (NatTrans.rightOp (Functor.whiskerLeft E τ)) U) hρ
  simp only [Functor.whiskerLeft_comp, NatTrans.rightOp_comp,
    Functor.whiskerRight_comp] at hU
  change (Functor.whiskerRight (NatTrans.rightOp (Functor.whiskerLeft E ρ)) U ≫
      (alternatingCofaceUnopIso A).inv) ≫
    ((alternatingCofaceUnopIso A).hom ≫ Functor.whiskerRight
      (NatTrans.rightOp (Functor.whiskerLeft E (inclusionOfMooreComplex Aᵒᵖ))) U) =
    𝟙 ((E ⋙ normalizedMooreComplex Aᵒᵖ).rightOp ⋙ U)
  simpa [Category.assoc] using hU

/-- The cochain projection is a quasi-isomorphism by Dold--Kan. -/
instance normalizedCofaceMapProjection_app_quasiIso (X : CosimplicialObject A) :
    QuasiIso ((normalizedCofaceMapProjection A).app X) := by
  let S := (E).obj (op X)
  let e := DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := S)
  have : QuasiIso (inclusionOfMooreComplexMap S) := e.quasiIso_hom
  have : QuasiIso ((U).map (inclusionOfMooreComplexMap S).op) :=
    chainComplexUnopFunctor_map_quasiIso A _
  change QuasiIso ((alternatingCofaceUnopIso A).hom.app X ≫
    (U).map (inclusionOfMooreComplexMap S).op)
  rw [_root_.quasiIso_iff]
  intro i
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap,
    HomologicalComplex.homologyMap_comp]
  infer_instance

/-- The normalized inclusion is also a quasi-isomorphism. -/
instance inclusionOfNormalizedCofaceMapComplex_app_quasiIso (X : CosimplicialObject A) :
    QuasiIso ((inclusionOfNormalizedCofaceMapComplex A).app X) := by
  let S := (E).obj (op X)
  let e := DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := S)
  have : QuasiIso (DoldKan.PInftyToNormalizedMooreComplex S) := e.quasiIso_inv
  have : QuasiIso ((U).map (DoldKan.PInftyToNormalizedMooreComplex S).op) :=
    chainComplexUnopFunctor_map_quasiIso A _
  change QuasiIso ((U).map (DoldKan.PInftyToNormalizedMooreComplex S).op ≫
    (alternatingCofaceUnopIso A).inv.app X)
  rw [_root_.quasiIso_iff]
  intro i
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap,
    HomologicalComplex.homologyMap_comp]
  infer_instance

/-- The inclusion induces the natural cohomology isomorphism. -/
def normalizedCofaceHomologyIso (n : ℕ) :
    normalizedCofaceMapComplex A ⋙
        HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n ≅
      alternatingCofaceMapComplex A ⋙
        HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n := by
  let α := Functor.whiskerRight (inclusionOfNormalizedCofaceMapComplex A)
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n)
  letI : ∀ X : CosimplicialObject A, IsIso (α.app X) := fun X ↦ by
    change IsIso (HomologicalComplex.homologyMap
      ((inclusionOfNormalizedCofaceMapComplex A).app X) n)
    infer_instance
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The cohomology comparison is the homology map of the inclusion. -/
theorem normalizedCofaceHomologyIso_hom_app (n : ℕ) (X : CosimplicialObject A) :
    (normalizedCofaceHomologyIso A n).hom.app X =
      HomologicalComplex.homologyMap
        ((inclusionOfNormalizedCofaceMapComplex A).app X) n := rfl

/-- The normalized projector uses the existing given cochain projection and inclusion. -/
def normalizedCofaceProjector :
    alternatingCofaceMapComplex A ⟶ alternatingCofaceMapComplex A :=
  normalizedCofaceMapProjection A ≫ inclusionOfNormalizedCofaceMapComplex A

/-- The codegenerate projector is the complementary endomorphism. -/
def codegenerateCofaceProjector :
    alternatingCofaceMapComplex A ⟶ alternatingCofaceMapComplex A :=
  𝟙 _ - normalizedCofaceProjector A

/-- The inclusion and projection split in each given cosimplicial object. -/
@[reassoc]
theorem normalizedCoface_inclusion_projection_app (X : CosimplicialObject A) :
    (inclusionOfNormalizedCofaceMapComplex A).app X ≫
        (normalizedCofaceMapProjection A).app X =
      𝟙 ((normalizedCofaceMapComplex A).obj X) :=
  congrArg (fun α => α.app X) (inclusionOfNormalizedCofaceMapComplex_comp_projection A)

/-- The projector complement retains the given two normalization maps. -/
theorem codegenerateCofaceProjector_app (X : CosimplicialObject A) :
    (codegenerateCofaceProjector A).app X =
      𝟙 ((alternatingCofaceMapComplex A).obj X) -
        (normalizedCofaceMapProjection A).app X ≫
          (inclusionOfNormalizedCofaceMapComplex A).app X := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The codegenerate projector is exactly the transported simplicial Q∞. -/
theorem codegenerateCofaceProjector_app_eq_native (X : CosimplicialObject A) :
    (codegenerateCofaceProjector A).app X =
      ((alternatingCofaceUnopIso A).app X).hom ≫
        (chainComplexUnopFunctor A).map
          (DoldKan.QInfty (X := (cosimplicialSimplicialEquiv A).functor.obj (op X))).op ≫
        ((alternatingCofaceUnopIso A).app X).inv := by
  let S := (cosimplicialSimplicialEquiv A).functor.obj (op X)
  let a := (alternatingCofaceUnopIso A).app X
  let UF := chainComplexUnopFunctor A
  let K : ChainComplex Aᵒᵖ ℕ := (alternatingFaceMapComplex Aᵒᵖ).obj S
  let N : ChainComplex Aᵒᵖ ℕ := (normalizedMooreComplex Aᵒᵖ).obj S
  let P : K ⟶ K := DoldKan.PInfty (X := S)
  let Q : K ⟶ K := DoldKan.QInfty (X := S)
  let i : N ⟶ K := inclusionOfMooreComplexMap S
  let p : K ⟶ N := DoldKan.PInftyToNormalizedMooreComplex S
  have hpi : p ≫ i = P :=
    DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap S
  have hu : UF.map i.op ≫ UF.map p.op = UF.map P.op := by
    calc
      _ = UF.map (i.op ≫ p.op) := (UF.map_comp i.op p.op).symm
      _ = UF.map ((p ≫ i).op) :=
        congrArg (fun f : op K ⟶ op K => UF.map f) (op_comp (f := p) (g := i)).symm
      _ = _ := congrArg (fun f : K ⟶ K => UF.map f.op) hpi
  have hp : (normalizedCofaceMapProjection A).app X ≫
      (inclusionOfNormalizedCofaceMapComplex A).app X =
    a.hom ≫ UF.map P.op ≫ a.inv := by
    change (a.hom ≫ UF.map i.op) ≫ (UF.map p.op ≫ a.inv) = _
    simpa only [Category.assoc] using
      congrArg (fun f : UF.obj (op K) ⟶ UF.obj (op K) => a.hom ≫ f ≫ a.inv) hu
  letI : UF.Additive := by
    dsimp only [UF]
    infer_instance
  have hQP : Q = 𝟙 K - P := rfl
  have hq : UF.map Q.op = 𝟙 (UF.obj (op K)) - UF.map P.op := by
    calc
      _ = UF.map ((𝟙 K - P).op) :=
        congrArg (fun f : K ⟶ K => UF.map f.op) hQP
      _ = _ := by rw [op_sub, op_id, UF.map_sub, UF.map_id]
  change 𝟙 ((alternatingCofaceMapComplex A).obj X) -
      ((normalizedCofaceMapProjection A).app X ≫
        (inclusionOfNormalizedCofaceMapComplex A).app X) =
    a.hom ≫ UF.map Q.op ≫ a.inv
  rw [hp, hq]
  simp only [Preadditive.comp_sub, Preadditive.sub_comp,
    Category.comp_id, Category.id_comp, Category.assoc, a.hom_inv_id]
  let b : (alternatingCofaceMapComplex A).obj X ≅ UF.obj (op K) := a
  have hb : b.hom ≫ 𝟙 (UF.obj (op K)) ≫ b.inv =
      𝟙 ((alternatingCofaceMapComplex A).obj X) :=
    (congrArg (fun g : UF.obj (op K) ⟶ (alternatingCofaceMapComplex A).obj X => b.hom ≫ g)
      (Category.id_comp b.inv)).trans b.hom_inv_id
  change 𝟙 ((alternatingCofaceMapComplex A).obj X) - (b.hom ≫ UF.map P.op ≫ b.inv) =
    (b.hom ≫ 𝟙 (UF.obj (op K)) ≫ b.inv) - (b.hom ≫ UF.map P.op ≫ b.inv)
  exact congrArg
    (fun g : (alternatingCofaceMapComplex A).obj X ⟶ (alternatingCofaceMapComplex A).obj X =>
      g - (b.hom ≫ UF.map P.op ≫ b.inv)) hb.symm

/-- The given normalized inclusion is killed by every codegeneracy. -/
@[reassoc]
theorem inclusionOfNormalizedCofaceMapComplex_codegeneracy
    (X : CosimplicialObject A) (n : ℕ) (i : Fin (n + 1)) :
    ((inclusionOfNormalizedCofaceMapComplex A).app X).f (n + 1) ≫ X.σ i = 0 := by
  let S := (cosimplicialSimplicialEquiv A).functor.obj (op X)
  let r := DoldKan.PInftyToNormalizedMooreComplex S
  have hQ : DoldKan.QInfty (X := S) ≫ r = 0 :=
    splitComplement_comp_retraction (DoldKan.QInfty (X := S))
      (inclusionOfMooreComplexMap S) r
      (DoldKan.splitMonoInclusionOfMooreComplexMap S).id
      (NormalizedQuotient.Q_eq_splitComplement S)
  have hQf : (DoldKan.QInfty (X := S)).f (n + 1) ≫ r.f (n + 1) = 0 := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply] using
      congrArg (fun f => f.f (n + 1)) hQ
  have hσ : S.σ i ≫ r.f (n + 1) = 0 :=
    ((DoldKan.degeneraciesVanish_iff_QInfty_f_comp (X := S) (n := n + 1) (r.f (n + 1))).2
      hQf).σ_comp i
  rw [inclusionOfNormalizedCofaceMapComplex_app_f]
  change (r.f (n + 1)).unop ≫ (S.σ i).unop = 0
  simpa only [unop_comp, unop_zero] using congrArg (fun f => f.unop) hσ

/-- Native opposite Moore normalization is the kernel of the codegenerate projector. -/
def normalizedCofaceKernelIso (X : CosimplicialObject A) :
    kernel ((codegenerateCofaceProjector A).app X) ≅
      (normalizedCofaceMapComplex A).obj X :=
  kernelSplitComplementIso ((codegenerateCofaceProjector A).app X)
    ((inclusionOfNormalizedCofaceMapComplex A).app X)
    ((normalizedCofaceMapProjection A).app X)
    (normalizedCoface_inclusion_projection_app A X)
    (codegenerateCofaceProjector_app A X)

/-- The kernel comparison keeps the normalized cochain inclusion. -/
@[reassoc]
theorem normalizedCofaceKernelIso_hom_inclusion (X : CosimplicialObject A) :
    (normalizedCofaceKernelIso A X).hom ≫
        (inclusionOfNormalizedCofaceMapComplex A).app X =
      kernel.ι ((codegenerateCofaceProjector A).app X) :=
  kernelSplitComplementIso_hom_ι ((codegenerateCofaceProjector A).app X)
    ((inclusionOfNormalizedCofaceMapComplex A).app X)
    ((normalizedCofaceMapProjection A).app X)
    (normalizedCoface_inclusion_projection_app A X)
    (codegenerateCofaceProjector_app A X)

/-- The same existing normalization is the cokernel of the codegenerate projector. -/
def normalizedCofaceCokernelIso (X : CosimplicialObject A) :
    cokernel ((codegenerateCofaceProjector A).app X) ≅
      (normalizedCofaceMapComplex A).obj X :=
  cokernelSplitComplementIso ((codegenerateCofaceProjector A).app X)
    ((inclusionOfNormalizedCofaceMapComplex A).app X)
    ((normalizedCofaceMapProjection A).app X)
    (normalizedCoface_inclusion_projection_app A X)
    (codegenerateCofaceProjector_app A X)

/-- The cokernel comparison keeps the given cochain projection. -/
@[reassoc]
theorem cokernel_π_normalizedCofaceCokernelIso_hom (X : CosimplicialObject A) :
    cokernel.π ((codegenerateCofaceProjector A).app X) ≫
        (normalizedCofaceCokernelIso A X).hom =
      (normalizedCofaceMapProjection A).app X :=
  cokernelSplitComplementIso_π_hom ((codegenerateCofaceProjector A).app X)
    ((inclusionOfNormalizedCofaceMapComplex A).app X)
    ((normalizedCofaceMapProjection A).app X)
    (normalizedCoface_inclusion_projection_app A X)
    (codegenerateCofaceProjector_app A X)

/-- Original cosimplicial maps induce the normalized kernel maps. -/
@[reassoc]
theorem normalizedCofaceKernelIso_naturality {X Y : CosimplicialObject A} (f : X ⟶ Y) :
    kernel.map ((codegenerateCofaceProjector A).app X)
        ((codegenerateCofaceProjector A).app Y)
        ((alternatingCofaceMapComplex A).map f) ((alternatingCofaceMapComplex A).map f)
        ((codegenerateCofaceProjector A).naturality f).symm ≫
      (normalizedCofaceKernelIso A Y).hom =
    (normalizedCofaceKernelIso A X).hom ≫ (normalizedCofaceMapComplex A).map f :=
  kernelSplitComplementIso_naturality ((codegenerateCofaceProjector A).app X)
    ((inclusionOfNormalizedCofaceMapComplex A).app X)
    ((normalizedCofaceMapProjection A).app X)
    (normalizedCoface_inclusion_projection_app A X) (codegenerateCofaceProjector_app A X)
    ((codegenerateCofaceProjector A).app Y)
    ((inclusionOfNormalizedCofaceMapComplex A).app Y)
    ((normalizedCofaceMapProjection A).app Y)
    (normalizedCoface_inclusion_projection_app A Y) (codegenerateCofaceProjector_app A Y)
    ((alternatingCofaceMapComplex A).map f) ((normalizedCofaceMapComplex A).map f)
    ((codegenerateCofaceProjector A).naturality f).symm
    ((inclusionOfNormalizedCofaceMapComplex A).naturality f).symm

/-- Original cosimplicial maps likewise induce the normalized cokernel maps. -/
@[reassoc]
theorem normalizedCofaceCokernelIso_naturality {X Y : CosimplicialObject A} (f : X ⟶ Y) :
    cokernel.map ((codegenerateCofaceProjector A).app X)
        ((codegenerateCofaceProjector A).app Y)
        ((alternatingCofaceMapComplex A).map f) ((alternatingCofaceMapComplex A).map f)
        ((codegenerateCofaceProjector A).naturality f).symm ≫
      (normalizedCofaceCokernelIso A Y).hom =
    (normalizedCofaceCokernelIso A X).hom ≫ (normalizedCofaceMapComplex A).map f :=
  cokernelSplitComplementIso_naturality ((codegenerateCofaceProjector A).app X)
    ((inclusionOfNormalizedCofaceMapComplex A).app X)
    ((normalizedCofaceMapProjection A).app X)
    (normalizedCoface_inclusion_projection_app A X) (codegenerateCofaceProjector_app A X)
    ((codegenerateCofaceProjector A).app Y)
    ((inclusionOfNormalizedCofaceMapComplex A).app Y)
    ((normalizedCofaceMapProjection A).app Y)
    (normalizedCoface_inclusion_projection_app A Y) (codegenerateCofaceProjector_app A Y)
    ((alternatingCofaceMapComplex A).map f) ((normalizedCofaceMapComplex A).map f)
    ((codegenerateCofaceProjector A).naturality f).symm
    ((normalizedCofaceMapProjection A).naturality f)

section AdditiveFunctorTransport

universe uD vD

variable {D : Type uD} [Category.{vD} D] [Abelian D] (F : A ⥤ D) [F.Additive]

/-- The existing opposite-Moore normalization commutes with every additive functor. -/
def normalizedCofaceCompMapIso :
    normalizedCofaceMapComplex A ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ) ≅
      ((CosimplicialObject.whiskering A D).obj F) ⋙ normalizedCofaceMapComplex D := by
  let EC := (cosimplicialSimplicialEquiv A).functor
  let ED := (cosimplicialSimplicialEquiv D).functor
  let S := (SimplicialObject.whiskering Aᵒᵖ Dᵒᵖ).obj F.op
  let T := (CosimplicialObject.whiskering A D).obj F
  let H := (F.op).mapHomologicalComplex (ComplexShape.down ℕ)
  let NC := normalizedMooreComplex Aᵒᵖ
  let ND := normalizedMooreComplex Dᵒᵖ
  let e : (EC ⋙ NC) ⋙ H ≅ T.op ⋙ (ED ⋙ ND) :=
    Functor.associator EC NC H ≪≫
      isoWhiskerLeft EC (NormalizedQuotient.mooreCompMapIso F.op) ≪≫
      (Functor.associator EC S ND).symm ≪≫
      isoWhiskerRight (cosimplicialSimplicialWhiskeringIso A F) ND ≪≫
      Functor.associator T.op ED ND
  exact Functor.associator (EC ⋙ NC).rightOp (chainComplexUnopFunctor A)
      (F.mapHomologicalComplex (ComplexShape.up ℕ)) ≪≫
    isoWhiskerLeft (EC ⋙ NC).rightOp (chainComplexUnopFunctorCompMapIso A F) ≪≫
    (Functor.associator (EC ⋙ NC).rightOp H.op (chainComplexUnopFunctor D)).symm ≪≫
    isoWhiskerRight (Functor.rightOpComp (EC ⋙ NC) H).symm (chainComplexUnopFunctor D) ≪≫
    isoWhiskerRight (NatIso.rightOp e.symm) (chainComplexUnopFunctor D) ≪≫
    isoWhiskerRight (Functor.rightOpCompOp T (ED ⋙ ND)) (chainComplexUnopFunctor D) ≪≫
    Functor.associator T (ED ⋙ ND).rightOp (chainComplexUnopFunctor D)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The given cochain comparison is the unop of the earned inverse Moore comparison. -/
theorem normalizedCofaceCompMapIso_hom_app_f (X : CosimplicialObject A) (n : ℕ) :
    ((normalizedCofaceCompMapIso A F).hom.app X).f n =
      (((NormalizedQuotient.mooreCompMapIso F.op).inv.app
        ((cosimplicialSimplicialEquiv A).functor.obj (op X))).f n).unop := by
  let EC := (cosimplicialSimplicialEquiv A).functor
  let ED := (cosimplicialSimplicialEquiv D).functor
  let S := (SimplicialObject.whiskering Aᵒᵖ Dᵒᵖ).obj F.op
  let T := (CosimplicialObject.whiskering A D).obj F
  let H := (F.op).mapHomologicalComplex (ComplexShape.down ℕ)
  let NC := normalizedMooreComplex Aᵒᵖ
  let ND := normalizedMooreComplex Dᵒᵖ
  let e : (EC ⋙ NC) ⋙ H ≅ T.op ⋙ (ED ⋙ ND) :=
    Functor.associator EC NC H ≪≫
      isoWhiskerLeft EC (NormalizedQuotient.mooreCompMapIso F.op) ≪≫
      (Functor.associator EC S ND).symm ≪≫
      isoWhiskerRight (cosimplicialSimplicialWhiskeringIso A F) ND ≪≫
      Functor.associator T.op ED ND
  let W := S.obj (EC.obj (op X))
  let V := H.obj (NC.obj (EC.obj (op X)))
  let t : W ⟶ W := (cosimplicialSimplicialWhiskeringIso A F).inv.app (op X)
  have ht : t = 𝟙 W := rfl
  have hNt : ND.map t = 𝟙 (ND.obj W) :=
    (congrArg (fun f : W ⟶ W => ND.map f) ht).trans (ND.map_id W)
  let k : ND.obj W ⟶ V :=
    (NormalizedQuotient.mooreCompMapIso F.op).inv.app (EC.obj (op X))
  have he : (e.inv.app (op X)).f n =
      k.f n := by
    change ((((𝟙 (ND.obj W) ≫ ND.map t) ≫ 𝟙 (ND.obj W)) ≫ k) ≫ 𝟙 V).f n = k.f n
    rw [hNt]
    simp only [Category.id_comp, Category.comp_id]
  let Y := F.obj (((NC.obj (EC.obj (op X))).X n).unop)
  let Z := ((ND.obj W).X n).unop
  let κ : Y ⟶ Y := ((chainComplexUnopFunctorCompMapIso A F).hom.app
    (op (NC.obj (EC.obj (op X))))).f n
  let ν : Y ⟶ Z := ((e.inv.app (op X)).f n).unop
  let ξ : Y ⟶ Z := (k.f n).unop
  have hκ : κ = 𝟙 Y :=
    chainComplexUnopFunctorCompMapIso_hom_app_f A F (op (NC.obj (EC.obj (op X)))) n
  have hν : ν = ξ :=
    congrArg (fun f : op Z ⟶ op Y => f.unop)
      (show ((e.inv.app (op X)).f n : op Z ⟶ op Y) = k.f n from he)
  change 𝟙 Y ≫ κ ≫ 𝟙 Y ≫ 𝟙 Y ≫ ν ≫ 𝟙 Z ≫ 𝟙 Z = ξ
  rw [hκ, hν]
  simp only [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The additive-functor comparison retains the given cochain projection. -/
@[reassoc]
theorem normalizedCofaceCompMapIso_projection (X : CosimplicialObject A) :
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((normalizedCofaceMapProjection A).app X) ≫
      (normalizedCofaceCompMapIso A F).hom.app X =
    (alternatingCofaceCompMapIso A F).hom.app X ≫
      (normalizedCofaceMapProjection D).app
        (((CosimplicialObject.whiskering A D).obj F).obj X) := by
  let S := (cosimplicialSimplicialEquiv A).functor.obj (op X)
  let T := ((SimplicialObject.whiskering Aᵒᵖ Dᵒᵖ).obj F.op).obj S
  let H := (F.op).mapHomologicalComplex (ComplexShape.down ℕ)
  let e := (NormalizedQuotient.mooreCompMapIso F.op).app S
  let a := (alternatingFaceMapComplexCompMapHomologicalComplexIso F.op).app S
  have hi : e.hom ≫ inclusionOfMooreComplexMap T =
      H.map (inclusionOfMooreComplexMap S) ≫ a.hom :=
    NormalizedQuotient.mooreCompMapIso_hom_inclusion F.op S
  have hInv : e.inv ≫ H.map (inclusionOfMooreComplexMap S) =
      inclusionOfMooreComplexMap T ≫ a.inv := by
    apply (cancel_mono a.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hi, Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext n
  change F.map (((normalizedCofaceMapProjection A).app X).f n) ≫
      ((normalizedCofaceCompMapIso A F).hom.app X).f n =
    ((alternatingCofaceCompMapIso A F).hom.app X).f n ≫
      ((normalizedCofaceMapProjection D).app
        (((CosimplicialObject.whiskering A D).obj F).obj X)).f n
  erw [normalizedCofaceMapProjection_app_f A X n,
    normalizedCofaceCompMapIso_hom_app_f A F X n,
    alternatingCofaceCompMapIso_hom_app_f A F X n,
    normalizedCofaceMapProjection_app_f D
      (((CosimplicialObject.whiskering A D).obj F).obj X) n]
  simp only [Category.id_comp]
  have hn := congrArg (fun f => f.f n) hInv
  change e.inv.f n ≫ F.op.map ((inclusionOfMooreComplexMap S).f n) =
    (inclusionOfMooreComplexMap T).f n ≫ 𝟙 _ at hn
  rw [Category.comp_id] at hn
  change (e.inv.f n ≫ F.op.map ((inclusionOfMooreComplexMap S).f n)).unop =
    ((inclusionOfMooreComplexMap T).f n).unop
  exact congrArg (fun f => f.unop) hn

end AdditiveFunctorTransport

end Abelian

end AlgebraicTopology

end
