/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Functor.Derived.Opposite
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Left derived functors in the native opposite-plus model of bounded-above categories

Opposite categories and the native degree-negating cochain equivalence
turn bounded-above projective complexes into bounded-below injective
complexes. The existing right derived functor on Plus then gives a genuine
left derived functor, with its universal property transported by the
native opposite localization and the proved Kan-extension duality.

This file uses the opposite of native Plus as its bounded-above model.
It does not assert an unproved equivalence with the existing full
subcategory DerivedCategory.Minus. No resolution engine is added.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe uC vC uD vD

namespace CategoryTheory.DerivedCategory.BoundedAboveDual

variable (C : Type uC) [Category.{vC} C] [Abelian C]

/-- The actual bounded-above complex model obtained from native bounded-below opposite complexes. -/
abbrev Complex := (CochainComplex.Plus Cᵒᵖ)ᵒᵖ

variable [HasDerivedCategory Cᵒᵖ]

/-- The native opposite-plus localization model of the bounded-above derived category. -/
abbrev Derived := (DerivedCategory.Plus Cᵒᵖ)ᵒᵖ

/-- The opposite of the native Plus localization, with its actual quasi-isomorphism property. -/
def Q : Complex C ⥤ Derived C := (DerivedCategory.Plus.Q (C := Cᵒᵖ)).op

/-- The original class of quasi-isomorphisms transported through the opposite category. -/
abbrev quasiIso : MorphismProperty (Complex C) := (CochainComplex.Plus.quasiIso Cᵒᵖ).op

/-- The native opposite of Plus localization inverts precisely the transported quasi-isomorphisms. -/
instance localization : (Q C).IsLocalization (quasiIso C) := by
  dsimp only [Q, quasiIso]
  infer_instance

variable {C} {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory Dᵒᵖ] (F : C ⥤ D) [F.Additive]

/-- The native original additive functor on the opposite-plus cochain model. -/
def mapComplex : Complex C ⥤ Complex D := Functor.op ((Functor.op F).mapCochainComplexPlus)

variable [EnoughProjectives C]

/-- The genuine left derived functor, obtained from native right derivation on the opposite category. -/
def leftDerived : Derived C ⥤ Derived D := Functor.op ((Functor.op F).rightDerivedFunctorPlus)

/-- The original right-derived unit becomes the actual left-derived counit. -/
def counit : Q C ⋙ leftDerived F ⟶ mapComplex F ⋙ Q D :=
  NatTrans.op ((Functor.op F).rightDerivedFunctorPlusUnit)

/-- The constructed counit has the genuine native left-derived universal property. -/
theorem leftDerived_isLeftDerived :
    (leftDerived F).IsLeftDerivedFunctor (counit F) (quasiIso C) := by
  let L := DerivedCategory.Plus.Q (C := Cᵒᵖ)
  let G := F.op.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q (C := Dᵒᵖ)
  let RF := F.op.rightDerivedFunctorPlus
  let U : G ⟶ L ⋙ RF := F.op.rightDerivedFunctorPlusUnit
  let α : L.op ⋙ RF.op ⟶ G.op := (Functor.opComp L RF).inv ≫ NatTrans.op U
  change Functor.IsLeftDerivedFunctor (L := L.op) (F := G.op) RF.op
    (counit F) (CochainComplex.Plus.quasiIso Cᵒᵖ).op
  have hα : α = counit F := by
    apply NatTrans.ext
    funext X
    change 𝟙 _ ≫ (counit F).app X = (counit F).app X
    exact Category.id_comp _
  rw [← hα]
  exact Functor.isLeftDerivedFunctor_op_of_isRightDerived (L := L) (F := G)
    RF U (CochainComplex.Plus.quasiIso Cᵒᵖ)

end CategoryTheory.DerivedCategory.BoundedAboveDual

namespace CochainComplex

variable {C : Type uC} [Category.{vC} C] [Abelian C]

/-- The actual degree-negating opposite complex, placed in native Plus using its original bound. -/
def opPlusOfBoundedAbove (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    CochainComplex.Plus Cᵒᵖ := by
  let L := (opEquivalence C).functor.obj (op K)
  have hL : L.IsStrictlyGE (-d) := by
    rw [isStrictlyGE_iff]
    intro n hn
    change IsZero (op (K.X (-n)))
    have hlt : n < -d := by simpa using hn
    have hd : d < -n := by simpa only [neg_neg] using (neg_lt_neg hlt)
    exact (K.isZero_of_isStrictlyLE d (-n) hd).op
  exact ⟨L, -d, hL⟩

/-- The opposite of an actual bounded-above projective term is injective in its native reflected degree. -/
theorem opPlusOfBoundedAbove_term_injective (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ n : ℤ, Projective (K.X n)] (n : ℤ) :
    Injective ((opPlusOfBoundedAbove K d).obj.X n) := by
  change Injective (op (K.X (-n)))
  infer_instance

end CochainComplex

namespace CategoryTheory.DerivedCategory.BoundedAboveDual

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory Cᵒᵖ] [HasDerivedCategory Dᵒᵖ]
  [EnoughProjectives C] (F : C ⥤ D) [F.Additive]

/-- The original cochain complex in the native bounded-above opposite-plus model. -/
def ofBoundedAbove (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] : Complex C :=
  op (CochainComplex.opPlusOfBoundedAbove K d)

/-- Native injective computation on the opposite side earns invertibility on original projective complexes. -/
theorem counit_isIso_of_projective (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ n : ℤ, Projective (K.X n)] :
    IsIso ((counit F).app (ofBoundedAbove K d)) := by
  let P := CochainComplex.opPlusOfBoundedAbove K d
  let hInjective : ∀ n : ℤ, Injective (P.obj.X n) :=
    CochainComplex.opPlusOfBoundedAbove_term_injective K d
  let J : CochainComplex (InjectiveObject Cᵒᵖ) ℤ :=
    HomologicalComplex.liftObjectProperty (isInjective Cᵒᵖ) P.obj hInjective
  obtain ⟨n, hn⟩ := P.property
  have hJ : J.IsStrictlyGE n := by
    rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff J (InjectiveObject.ι Cᵒᵖ)]
    change P.obj.IsStrictlyGE n
    exact hn
  let JP : CochainComplex.Plus (InjectiveObject Cᵒᵖ) := ⟨J, n, hJ⟩
  let I := (InjectiveObject.ι Cᵒᵖ).mapCochainComplexPlus.obj JP
  let e : I ≅ P := ObjectProperty.isoMk (CochainComplex.plus Cᵒᵖ) (eqToIso (by rfl))
  let A := F.op.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q (C := Dᵒᵖ)
  let B := DerivedCategory.Plus.Q (C := Cᵒᵖ) ⋙ F.op.rightDerivedFunctorPlus
  let U : A ⟶ B := F.op.rightDerivedFunctorPlusUnit
  have hI : IsIso (U.app I) := by
    dsimp only [U, I]
    infer_instance
  have hP : U.app P = A.map e.inv ≫ U.app I ≫ B.map e.hom := by
    rw [← U.naturality e.hom, ← A.map_comp_assoc, e.inv_hom_id, A.map_id, Category.id_comp]
  have hUnit : IsIso (U.app P) := by
    rw [hP]
    infer_instance
  change IsIso ((U.app P).op)
  infer_instance

/-- The genuine derived computation isomorphism on an original bounded-above projective model. -/
def projectiveComputationIso (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ n : ℤ, Projective (K.X n)] :
    (leftDerived F).obj ((Q C).obj (ofBoundedAbove K d)) ≅
      (Q D).obj ((mapComplex F).obj (ofBoundedAbove K d)) := by
  letI := counit_isIso_of_projective F K d
  exact asIso ((counit F).app (ofBoundedAbove K d))

/-- Mapping the actual reflected cochain complex agrees with reflecting the original mapped complex. -/
def cochainOpMapIso (K : CochainComplex C ℤ) :
    (F.op.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.opEquivalence C).functor.obj (op K)) ≅
      (CochainComplex.opEquivalence D).functor.obj
        (op ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  eqToIso (by rfl)

/-- The actual original mapped complex, placed in the bounded-above model by native opposite transport. -/
def actualMappedComplex (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] : Complex D := by
  let P := F.op.mapCochainComplexPlus.obj (CochainComplex.opPlusOfBoundedAbove K d)
  refine op ⟨(CochainComplex.opEquivalence D).functor.obj
    (op ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)), ?_⟩
  obtain ⟨n, hn⟩ := P.property
  have hSource : CochainComplex.IsStrictlyGE
      ((F.op.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.opEquivalence C).functor.obj (op K))) n := by
    change P.obj.IsStrictlyGE n
    exact hn
  let _ : CochainComplex.IsStrictlyGE
      ((F.op.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.opEquivalence C).functor.obj (op K))) n := hSource
  exact ⟨n, CochainComplex.isStrictlyGE_of_iso (cochainOpMapIso F K) n⟩

/-- The original additive map on bounded-above complexes has its actual componentwise reflected comparison. -/
def mappedComplexIso (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    (mapComplex F).obj (ofBoundedAbove K d) ≅ actualMappedComplex F K d := by
  let e : F.op.mapCochainComplexPlus.obj (CochainComplex.opPlusOfBoundedAbove K d) ≅
      unop (actualMappedComplex F K d) :=
    ObjectProperty.isoMk (CochainComplex.plus Dᵒᵖ) (cochainOpMapIso F K)
  exact e.op.symm

/-- On a genuine projective source, the left derived value is the image of the actual original mapped complex. -/
def projectiveActualComplexIso (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ n : ℤ, Projective (K.X n)] :
    (leftDerived F).obj ((Q C).obj (ofBoundedAbove K d)) ≅
      (Q D).obj (actualMappedComplex F K d) :=
  projectiveComputationIso F K d ≪≫ (Q D).mapIso (mappedComplexIso F K d)

end CategoryTheory.DerivedCategory.BoundedAboveDual

end
