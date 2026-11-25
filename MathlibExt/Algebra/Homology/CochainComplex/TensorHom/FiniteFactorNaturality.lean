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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.HomTensorNaturality
public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.FiniteFactorIso
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering

/-!
# Finite tensor-factor cochain natural isomorphisms

The source and target use the Hom and tensor functors, and the natural
transformation is the signed comparison. Only U is restricted to bounded
cochains with finite categorical-projective terms; its inclusion retains
all maps. The cochain object isomorphism gives componentwise invertibility.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]

/-- All original cochain triples, with only the first Hom source opposite. -/
abbrev HomTensorCoChainTriples :=
  ((CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ ×
    CochainComplex (ModuleCat.{v} R) ℤ) × CochainComplex (ModuleCat.{v} R) ℤ

/-- The actual original source functor T(H(P,J),U). -/
def homTensorCoChainLeftFunctor :
    HomTensorCoChainTriples.{u, v} R ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  ((CategoryTheory.Functor.uncurry.obj (linearFunctor R (ModuleCat.{v} R))).prod
      (𝟭 (CochainComplex (ModuleCat.{v} R) ℤ))) ⋙
    CategoryTheory.Functor.uncurry.obj
      (bifunctorAt R : CochainComplex (ModuleCat.{v} R) ℤ ⥤
        CochainComplex (ModuleCat.{v} R) ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ)

/-- The actual original target functor H(P,T(J,U)). -/
def homTensorCoChainRightFunctor :
    HomTensorCoChainTriples.{u, v} R ⥤ CochainComplex (ModuleCat.{v} R) ℤ := by
  let A : HomTensorCoChainTriples.{u, v} R ⥤
      (CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ :=
    CategoryTheory.Prod.fst
        ((CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ ×
          CochainComplex (ModuleCat.{v} R) ℤ)
        (CochainComplex (ModuleCat.{v} R) ℤ) ⋙
      CategoryTheory.Prod.fst
        (CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ
        (CochainComplex (ModuleCat.{v} R) ℤ)
  let B : HomTensorCoChainTriples.{u, v} R ⥤
      CochainComplex (ModuleCat.{v} R) ℤ :=
    ((CategoryTheory.Prod.snd
        (CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ
        (CochainComplex (ModuleCat.{v} R) ℤ)).prod
      (𝟭 (CochainComplex (ModuleCat.{v} R) ℤ))) ⋙
        CategoryTheory.Functor.uncurry.obj
          (bifunctorAt R : CochainComplex (ModuleCat.{v} R) ℤ ⥤
            CochainComplex (ModuleCat.{v} R) ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ)
  exact A.prod' B ⋙ CategoryTheory.Functor.uncurry.obj
    (linearFunctor R (ModuleCat.{v} R))

/-- The source functor has exactly the original tensor/Hom object. -/
theorem homTensorCoChainLeftFunctor_obj (X : HomTensorCoChainTriples.{u, v} R) :
    (homTensorCoChainLeftFunctor R).obj X =
      complexAt R (linearComplex R X.1.1.unop X.1.2) X.2 := rfl

/-- The target functor has exactly the original Hom/tensor object. -/
theorem homTensorCoChainRightFunctor_obj (X : HomTensorCoChainTriples.{u, v} R) :
    (homTensorCoChainRightFunctor R).obj X =
      linearComplex R X.1.1.unop (complexAt R X.1.2 X.2) := rfl

/-- Source functor maps are the mapAt/linearComplexMap maps. -/
theorem homTensorCoChainLeftFunctor_map
    {X Y : HomTensorCoChainTriples.{u, v} R} (f : X ⟶ Y) :
    (homTensorCoChainLeftFunctor R).map f =
      mapAt R (linearComplexMap R f.1.1.unop f.1.2) f.2 := by
  change (CategoryTheory.Functor.uncurry.obj
      (bifunctorAt R : CochainComplex (ModuleCat.{v} R) ℤ ⥤
        CochainComplex (ModuleCat.{v} R) ℤ ⥤
        CochainComplex (ModuleCat.{v} R) ℤ)).map
          (X := (linearComplex R X.1.1.unop X.1.2, X.2))
          (Y := (linearComplex R Y.1.1.unop Y.1.2, Y.2))
          ((CategoryTheory.Functor.uncurry.obj
            (linearFunctor R (ModuleCat.{v} R))).map
              (X := X.1) (Y := Y.1) f.1, f.2) = _
  rw [linearFunctor_uncurry_map, mapAt_uncurry]

/-- Every target functor map is the actual original pre/postcomposition map. -/
theorem homTensorCoChainRightFunctor_map
    {X Y : HomTensorCoChainTriples.{u, v} R} (f : X ⟶ Y) :
    (homTensorCoChainRightFunctor R).map f =
      linearComplexMap R f.1.1.unop (mapAt R f.1.2 f.2) := by
  change (CategoryTheory.Functor.uncurry.obj
      (linearFunctor R (ModuleCat.{v} R))).map
        (X := (X.1.1, complexAt R X.1.2 X.2))
        (Y := (Y.1.1, complexAt R Y.1.2 Y.2))
        (f.1.1, (CategoryTheory.Functor.uncurry.obj
          (bifunctorAt R : CochainComplex (ModuleCat.{v} R) ℤ ⥤
            CochainComplex (ModuleCat.{v} R) ℤ ⥤
            CochainComplex (ModuleCat.{v} R) ℤ)).map
              (X := (X.1.2, X.2)) (Y := (Y.1.2, Y.2)) (f.1.2, f.2)) = _
  rw [linearFunctor_uncurry_map, mapAt_uncurry]

/-- The unrestricted transformation is the actual original signed comparison. -/
def homTensorCoChainNatTrans :
    homTensorCoChainLeftFunctor.{u, v} R ⟶ homTensorCoChainRightFunctor.{u, v} R where
  app X := homTensorComparison R X.1.1.unop X.1.2 X.2
  naturality X Y f := by
    rw [homTensorCoChainLeftFunctor_map, homTensorCoChainRightFunctor_map]
    exact homTensorComparison_naturality R f.1.1.unop f.1.2 f.2

/-- Only the original U bounds and finite categorical-projective terms qualify a triple. -/
def finiteFactorHomTensorCoChainProperty : ObjectProperty (HomTensorCoChainTriples.{u, v} R) :=
  fun X => ∃ L N : ℤ,
    (∀ b : ℤ, b < L → IsZero (X.2.X b)) ∧
    (∀ b : ℤ, N < b → IsZero (X.2.X b)) ∧
    (∀ b : ℤ, CategoryTheory.Projective (X.2.X b)) ∧
    (∀ b : ℤ, Module.Finite R (X.2.X b))

/-- The native full subcategory retains all original maps between finite-C triples. -/
abbrev FiniteFactorHomTensorCoChainTriples :=
  (finiteFactorHomTensorCoChainProperty.{u, v} R).FullSubcategory

/-- The native inclusion forgets only the original finite-C qualification. -/
abbrev finiteFactorHomTensorCoChainInclusion :
    FiniteFactorHomTensorCoChainTriples.{u, v} R ⥤ HomTensorCoChainTriples.{u, v} R :=
  ObjectProperty.ι _

/-- The bounded-U object isomorphism gives invertibility of each component. -/
theorem homTensorCoChainNatTrans_app_isIso
    (X : FiniteFactorHomTensorCoChainTriples.{u, v} R) :
    IsIso ((homTensorCoChainNatTrans R).app X.obj) := by
  obtain ⟨L, N, hUlo, hUhi, hProj, hFinite⟩ := X.property
  let : ∀ b : ℤ, CategoryTheory.Projective (X.obj.2.X b) := hProj
  let : ∀ b : ℤ, Module.Finite R (X.obj.2.X b) := hFinite
  change IsIso (homTensorComparison R X.obj.1.1.unop X.obj.1.2 X.obj.2)
  rw [← finiteFactorHomTensorIso_hom R X.obj.1.1.unop X.obj.1.2 X.obj.2
    L N hUlo hUhi]
  infer_instance

/-- The natural Iso is the restriction of the original unrestricted signed transformation. -/
def finiteFactorHomTensorCoChainNatIso :
    finiteFactorHomTensorCoChainInclusion.{u, v} R ⋙ homTensorCoChainLeftFunctor R ≅
      finiteFactorHomTensorCoChainInclusion.{u, v} R ⋙ homTensorCoChainRightFunctor R := by
  let α := CategoryTheory.Functor.whiskerLeft
    (finiteFactorHomTensorCoChainInclusion R) (homTensorCoChainNatTrans R)
  letI : IsIso α := (NatTrans.isIso_iff_isIso_app α).2
    (fun X => homTensorCoChainNatTrans_app_isIso R X)
  exact asIso α

/-- Its whole hom is exactly the restricted original transformation. -/
theorem finiteFactorHomTensorCoChainNatIso_hom :
    (finiteFactorHomTensorCoChainNatIso.{u, v} R).hom =
      CategoryTheory.Functor.whiskerLeft
        (finiteFactorHomTensorCoChainInclusion R) (homTensorCoChainNatTrans R) := rfl

/-- Each hom component retains the actual original cochain comparison. -/
theorem finiteFactorHomTensorCoChainNatIso_hom_app
    (X : FiniteFactorHomTensorCoChainTriples.{u, v} R) :
    (finiteFactorHomTensorCoChainNatIso R).hom.app X =
      homTensorComparison R X.obj.1.1.unop X.obj.1.2 X.obj.2 := rfl

end CochainComplex.ModuleTensor
