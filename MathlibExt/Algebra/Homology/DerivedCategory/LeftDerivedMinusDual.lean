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
# Left derivation in the opposite bounded-below model

For an abelian category C, the opposite of bounded-below cochain complexes
over Cᵒᵖ is a bounded-above complex model.
With a chosen derived category of Cᵒᵖ, its localization is
D⁺(Cᵒᵖ)ᵒᵖ.

For additive F:C → D and enough projectives in C, the opposite
right-derived functor of Fᵒᵖ gives a left-derived functor on these
models. Its counit has the left-derived universal property.
Degree-negating reflection places a complex K zero above d in the
bounded-below opposite category, and termwise projectivity of K
makes the reflected terms injective. The counit is then invertible
and computes the derived value by the original mapped complex F(K).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe uC vC uD vD

namespace CategoryTheory.DerivedCategory.BoundedAboveDual

variable (C : Type uC) [Category.{vC} C] [Abelian C]

/-- Let C be abelian. Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ.

The bounded-above complex model C_-, whose objects are opposite bounded-below cochain complexes over
Cᵒᵖ. -/
abbrev Complex := (CochainComplex.Plus Cᵒᵖ)ᵒᵖ

variable [HasDerivedCategory Cᵒᵖ]

/-- Let C be abelian. Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ.

With a chosen derived category of Cᵒᵖ, the bounded-above derived model is D⁺(Cᵒᵖ)ᵒᵖ. -/
abbrev Derived := (DerivedCategory.Plus Cᵒᵖ)ᵒᵖ

/-- Let C be abelian. Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ.

With a chosen derived category of Cᵒᵖ, Q_- is the opposite of the bounded-below localization
Q_+:CochainComplex.Plus(Cᵒᵖ) → D⁺(Cᵒᵖ). -/
def Q : Complex C ⥤ Derived C := (DerivedCategory.Plus.Q (C := Cᵒᵖ)).op

/-- Let C be abelian. Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ.

The quasi-isomorphism class in C_- is the opposite of the quasi-isomorphism class on bounded-below
Cᵒᵖ-complexes. -/
abbrev quasiIso : MorphismProperty (Complex C) := (CochainComplex.Plus.quasiIso Cᵒᵖ).op

/-- Let C be abelian. Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ.

With a chosen derived category of Cᵒᵖ, Q_-:C_- → D⁺(Cᵒᵖ)ᵒᵖ localizes at the transported
quasi-isomorphisms. -/
instance localization : (Q C).IsLocalization (quasiIso C) := by
  dsimp only [Q, quasiIso]
  infer_instance

variable {C} {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory Dᵒᵖ] (F : C ⥤ D) [F.Additive]

/-- For abelian C,D and additive F:C → D, the functor between their
bounded-above complex models is the opposite of termwise application
of Fᵒᵖ to bounded-below Cᵒᵖ-complexes. -/
def mapComplex : Complex C ⥤ Complex D := Functor.op ((Functor.op F).mapCochainComplexPlus)

variable [EnoughProjectives C]

/-- Let C,D be abelian with chosen derived categories for Cᵒᵖ,Dᵒᵖ,
F:C → D additive and C having enough projectives.
Set D_-^op(C)=D⁺(Cᵒᵖ)ᵒᵖ and similarly for D.

The left-derived functor D_-^op(C) → D_-^op(D) is the opposite of the right-derived functor of Fᵒᵖ
on bounded-below objects. -/
def leftDerived : Derived C ⥤ Derived D := Functor.op ((Functor.op F).rightDerivedFunctorPlus)

/-- Let C,D be abelian with chosen derived categories for Cᵒᵖ,Dᵒᵖ,
F:C → D additive and C having enough projectives.
Set D_-^op(C)=D⁺(Cᵒᵖ)ᵒᵖ and similarly for D.

The opposite right-derived unit gives the counit Q_-∘LF → mapComplex(F)∘Q_-, on the bounded-above
complex model. -/
def counit : Q C ⋙ leftDerived F ⟶ mapComplex F ⋙ Q D :=
  NatTrans.op ((Functor.op F).rightDerivedFunctorPlusUnit)

/-- Let C,D be abelian with chosen derived categories for Cᵒᵖ,Dᵒᵖ,
F:C → D additive and C having enough projectives.
Set D_-^op(C)=D⁺(Cᵒᵖ)ᵒᵖ and similarly for D.

The constructed LF and counit satisfy the left-derived universal property relative to
quasi-isomorphisms of the bounded-above model. -/
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

/-- Let C be abelian and K a cochain complex zero above d∈ℤ.
Degree-negating opposite reflection gives a bounded-below Cᵒᵖ-complex,
with degree-n term op(K^{−n}) and lower term bound −d. -/
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

/-- Let C be abelian, K zero above d and every K^n projective.
Every term of its degree-negating Cᵒᵖ-reflection is injective. -/
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

/-- Let C be abelian. Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ.

A complex K zero above d gives the object of C_- opposite to its bounded-below Cᵒᵖ-reflection. -/
def ofBoundedAbove (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] : Complex C :=
  op (CochainComplex.opPlusOfBoundedAbove K d)

/-- Let C,D be abelian with chosen derived categories for Cᵒᵖ,Dᵒᵖ,
F:C → D additive and C having enough projectives.
Set D_-^op(C)=D⁺(Cᵒᵖ)ᵒᵖ and similarly for D.

For K zero above d and projective in every degree, the left-derived counit at its bounded-above
model object is an isomorphism. -/
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

/-- Let C,D be abelian with chosen derived categories for Cᵒᵖ,Dᵒᵖ,
F:C → D additive and C having enough projectives.
Set D_-^op(C)=D⁺(Cᵒᵖ)ᵒᵖ and similarly for D.

For K zero above d and termwise projective, the canonical isomorphism from LF(Q_-(K)) to Q_- applied
to its mapped bounded-above model. -/
def projectiveComputationIso (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ n : ℤ, Projective (K.X n)] :
    (leftDerived F).obj ((Q C).obj (ofBoundedAbove K d)) ≅
      (Q D).obj ((mapComplex F).obj (ofBoundedAbove K d)) := by
  letI := counit_isIso_of_projective F K d
  exact asIso ((counit F).app (ofBoundedAbove K d))

/-- For abelian C,D and additive F:C → D, termwise application of Fᵒᵖ
to the degree-negating reflection of K is canonically isomorphic to
the degree-negating reflection of the original mapped complex F(K). -/
def cochainOpMapIso (K : CochainComplex C ℤ) :
    (F.op.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.opEquivalence C).functor.obj (op K)) ≅
      (CochainComplex.opEquivalence D).functor.obj
        (op ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  eqToIso (by rfl)

/-- For abelian C,D and additive F:C → D, if K is zero above d,
the reflected mapped complex F(K), viewed oppositely, is an object
of the bounded-above complex model for D. -/
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

/-- For abelian C,D and additive F:C → D, a complex K zero above d has
a canonical isomorphism between its image in the bounded-above model
under F and the model of the actual termwise mapped complex F(K). -/
def mappedComplexIso (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    (mapComplex F).obj (ofBoundedAbove K d) ≅ actualMappedComplex F K d := by
  let e : F.op.mapCochainComplexPlus.obj (CochainComplex.opPlusOfBoundedAbove K d) ≅
      unop (actualMappedComplex F K d) :=
    ObjectProperty.isoMk (CochainComplex.plus Dᵒᵖ) (cochainOpMapIso F K)
  exact e.op.symm

/-- Let C,D be abelian with chosen derived categories for Cᵒᵖ,Dᵒᵖ,
F:C → D additive and C having enough projectives.
Set D_-^op(C)=D⁺(Cᵒᵖ)ᵒᵖ and similarly for D.

For K zero above d and projective in every degree, LF(Q_-(K)) is canonically isomorphic to Q_- of
the bounded-above model of the actual complex F(K). -/
def projectiveActualComplexIso (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ n : ℤ, Projective (K.X n)] :
    (leftDerived F).obj ((Q C).obj (ofBoundedAbove K d)) ≅
      (Q D).obj (actualMappedComplex F K d) :=
  projectiveComputationIso F K d ≪≫ (Q D).mapIso (mappedComplexIso F K d)

end CategoryTheory.DerivedCategory.BoundedAboveDual

end
