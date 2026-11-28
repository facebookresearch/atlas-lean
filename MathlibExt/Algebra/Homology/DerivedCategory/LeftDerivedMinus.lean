/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.DerivedCategory.MinusOppositeEquivalence
public import MathlibExt.Algebra.Homology.DerivedCategory.LeftDerivedMinusDual

/-!
# Left derivation on the bounded-above derived category

Let C,D be abelian with chosen derived categories for both categories and
their opposites. The opposite of bounded-below cochain complexes over Cᵒᵖ
is a bounded-above complex model, with localization Q_C into D⁻(C).

For additive F:C → D and enough projectives in C, opposite right derivation
and the bounded-above/opposite-bounded-below equivalences give
LF:D⁻(C) → D⁻(D), with counit Q_C∘LF → U_F, where U_F is the mapped
complex followed by localization. This counit has the left-derived
universal property.

For a complex K zero above d and projective in every degree,
LF([K]) is canonically the derived object of the termwise mapped
complex F(K). Category and derived-category universes remain independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.DerivedCategory Opposite

universe uC vC uD vD wC wCo wD wDo

namespace DerivedCategory.CanonicalLeft

variable (C : Type uC) [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wCo} Cᵒᵖ]

/-- Let C be abelian with chosen derived categories for C and Cᵒᵖ.
The localization from C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ to D⁻(C),
obtained from opposite bounded-below localization and the inverse
bounded-above/opposite-plus equivalence. -/
def Q : BoundedAboveDual.Complex C ⥤ DerivedCategory.Minus C :=
  BoundedAboveDual.Q C ⋙ (DerivedCategory.minusOppositeEquivalence C).inverse

/-- For an abelian category C with chosen derived categories for C and Cᵒᵖ,
Q_C:C_- → D⁻(C) is a localization at the quasi-isomorphisms of the
bounded-above complex model. -/
instance localization : (Q C).IsLocalization (BoundedAboveDual.quasiIso C) :=
  Functor.IsLocalization.of_equivalence_target (BoundedAboveDual.Q C)
    (BoundedAboveDual.quasiIso C) (Q C)
      (DerivedCategory.minusOppositeEquivalence C).symm (Iso.refl _)

variable {C} {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wDo} Dᵒᵖ]
  [EnoughProjectives C] (F : C ⥤ D) [F.Additive]

/-- Let C,D be abelian with independently chosen derived categories
for C,Cᵒᵖ,D,Dᵒᵖ, and F:C → D additive.
Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ for the bounded-above
complex model, and Q_C:C_- → D⁻(C) for its localization.

The underived functor U_F:C_- → D⁻(D) maps the bounded-above complex model by F and then applies
Q_D. -/
def underived : BoundedAboveDual.Complex C ⥤ DerivedCategory.Minus D :=
  BoundedAboveDual.mapComplex F ⋙ Q D

/-- Let C,D be abelian with independently chosen derived categories
for C,Cᵒᵖ,D,Dᵒᵖ, and F:C → D additive.
Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ for the bounded-above
complex model, and Q_C:C_- → D⁻(C) for its localization. Assume C has enough projectives.

The left-derived functor LF:D⁻(C) → D⁻(D), obtained from opposite right derivation through the
bounded-above/opposite-plus equivalences. -/
def leftDerived : DerivedCategory.Minus C ⥤ DerivedCategory.Minus D :=
  (DerivedCategory.minusOppositeEquivalence C).functor ⋙
    (BoundedAboveDual.leftDerived F ⋙ (DerivedCategory.minusOppositeEquivalence D).inverse)

/-- Let C,D be abelian with independently chosen derived categories
for C,Cᵒᵖ,D,Dᵒᵖ, and F:C → D additive.
Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ for the bounded-above
complex model, and Q_C:C_- → D⁻(C) for its localization. Assume C has enough projectives.

The opposite-plus left-derived functor followed by the target equivalence into D⁻(D), with domain
D⁺(Cᵒᵖ)ᵒᵖ. -/
abbrev postDerived : BoundedAboveDual.Derived C ⥤ DerivedCategory.Minus D :=
  BoundedAboveDual.leftDerived F ⋙ (DerivedCategory.minusOppositeEquivalence D).inverse

/-- Let C,D be abelian with independently chosen derived categories
for C,Cᵒᵖ,D,Dᵒᵖ, and F:C → D additive.
Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ for the bounded-above
complex model, and Q_C:C_- → D⁻(C) for its localization. Assume C has enough projectives.

Precomposing LF by the inverse equivalence D⁺(Cᵒᵖ)ᵒᵖ → D⁻(C) is naturally isomorphic to the
opposite-plus derived functor followed by the target equivalence. -/
def localizationComputationIso :
    (DerivedCategory.minusOppositeEquivalence C).inverse ⋙ leftDerived F ≅ postDerived F :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.minusOppositeEquivalence C).counitIso
      (postDerived F) ≪≫
    Functor.leftUnitor _

/-- Let C,D be abelian with independently chosen derived categories
for C,Cᵒᵖ,D,Dᵒᵖ, and F:C → D additive.
Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ for the bounded-above
complex model, and Q_C:C_- → D⁻(C) for its localization. Assume C has enough projectives.

The canonical counit Q_C∘LF → U_F, induced by the opposite right-derived unit and the model
equivalences. -/
def counit : Q C ⋙ leftDerived F ⟶ underived F :=
  (Functor.associator _ _ _).hom ≫
    (Functor.isoWhiskerLeft (BoundedAboveDual.Q C) (localizationComputationIso F)).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (BoundedAboveDual.counit F)
      (DerivedCategory.minusOppositeEquivalence D).inverse

/-- Let C,D be abelian with independently chosen derived categories
for C,Cᵒᵖ,D,Dᵒᵖ, and F:C → D additive.
Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ for the bounded-above
complex model, and Q_C:C_- → D⁻(C) for its localization. Assume C has enough projectives.

LF with its counit Q_C∘LF → U_F is a left-derived functor of U_F relative to the quasi-isomorphisms
of C_-. -/
theorem leftDerived_isLeftDerived :
    (leftDerived F).IsLeftDerivedFunctor (counit F) (BoundedAboveDual.quasiIso C) := by
  let _ : Functor.IsLeftDerivedFunctor (L := BoundedAboveDual.Q C)
      (F := BoundedAboveDual.mapComplex F ⋙ BoundedAboveDual.Q D)
      (BoundedAboveDual.leftDerived F) (BoundedAboveDual.counit F) (BoundedAboveDual.quasiIso C) :=
    BoundedAboveDual.leftDerived_isLeftDerived F
  let _ : (DerivedCategory.minusOppositeEquivalence D).inverse.IsRightAdjoint :=
    (DerivedCategory.minusOppositeEquivalence D).isRightAdjoint_inverse
  let τ : BoundedAboveDual.Q C ⋙ postDerived F ⟶ underived F :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (BoundedAboveDual.counit F)
        (DerivedCategory.minusOppositeEquivalence D).inverse
  have h : Functor.IsLeftDerivedFunctor (L := BoundedAboveDual.Q C) (F := underived F)
      (postDerived F) τ (BoundedAboveDual.quasiIso C) := by
    change Functor.IsLeftDerivedFunctor (L := BoundedAboveDual.Q C)
      (F := (BoundedAboveDual.mapComplex F ⋙ BoundedAboveDual.Q D) ⋙
        (DerivedCategory.minusOppositeEquivalence D).inverse)
      (BoundedAboveDual.leftDerived F ⋙ (DerivedCategory.minusOppositeEquivalence D).inverse)
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight (BoundedAboveDual.counit F)
        (DerivedCategory.minusOppositeEquivalence D).inverse) (BoundedAboveDual.quasiIso C)
    infer_instance
  exact (LocalizerMorphism.isLeftDerivedFunctor_iff_precomp
    (LocalizerMorphism.id (BoundedAboveDual.quasiIso C))
    (BoundedAboveDual.Q C) (Q C) (DerivedCategory.minusOppositeEquivalence C).inverse
    (Functor.leftUnitor _) τ (counit F)
    (Functor.leftUnitor _) (localizationComputationIso F) (by
      apply NatTrans.ext
      funext K
      have hCu : (counit F).app K =
          (localizationComputationIso F).hom.app ((BoundedAboveDual.Q C).obj K) ≫ τ.app K := by
        change 𝟙 _ ≫ (localizationComputationIso F).hom.app ((BoundedAboveDual.Q C).obj K) ≫
            𝟙 _ ≫ (DerivedCategory.minusOppositeEquivalence D).inverse.map
              ((BoundedAboveDual.counit F).app K) =
          (localizationComputationIso F).hom.app ((BoundedAboveDual.Q C).obj K) ≫
            𝟙 _ ≫ (DerivedCategory.minusOppositeEquivalence D).inverse.map
              ((BoundedAboveDual.counit F).app K)
        simp only [Category.id_comp]
      change τ.app K = (localizationComputationIso F).inv.app ((BoundedAboveDual.Q C).obj K) ≫
        𝟙 _ ≫ (leftDerived F).map (𝟙 ((Q C).obj K)) ≫ 𝟙 _ ≫ (counit F).app K ≫ 𝟙 _
      have hMapId : (leftDerived F).map (𝟙 ((Q C).obj K)) = 𝟙 _ := (leftDerived F).map_id _
      dsimp only [Q, Functor.comp_obj] at hMapId hCu ⊢
      rw [hMapId, hCu]
      simp only [Category.id_comp, Category.comp_id, Category.assoc,
        Iso.inv_hom_id_app_assoc])).2 h

/-- Let C be abelian with a chosen derived category and K an integer
cochain complex whose terms are zero in degrees above d∈ℤ.
Its localization [K] is an object of the cohomologically bounded-above
subcategory D⁻(C). -/
def objectOfBoundedAbove (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    DerivedCategory.Minus C :=
  { obj := DerivedCategory.Q.obj K
    property := ⟨d, inferInstance⟩ }

/-- Let C be abelian with chosen derived categories for C,Cᵒᵖ and let
K be zero in degrees above d. The canonical isomorphism between
Q_C applied to K's bounded-above complex model and its original
derived object [K] in D⁻(C). -/
def nativeLocalizationIso (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    (Q C).obj (BoundedAboveDual.ofBoundedAbove K d) ≅ objectOfBoundedAbove (C := C) K d := by
  let E := DerivedCategory.minusOppositeEquivalence C
  let P := CochainComplex.opPlusOfBoundedAbove K d
  have hRaw : OppositeTransport.reflect C (DerivedCategory.Q.obj K) ≅
      (DerivedCategory.Q (C := Cᵒᵖ)).obj P.obj := by
    change (OppositeTransport.equivalence C).functor.obj (op (DerivedCategory.Q.obj K)) ≅ _
    rw [OppositeTransport.equivalence_functor_eq]
    have hPobj : P.obj = (OppositeTransport.cochainEquivalence C).functor.obj (op K) := rfl
    rw [hPobj]
    simpa only [Functor.comp_obj, Functor.op_obj] using (OppositeTransport.forwardFac C).app (op K)
  have hPlus : ((DerivedCategory.Plus.Q (C := Cᵒᵖ)).obj P).obj ≅
      (DerivedCategory.Q (C := Cᵒᵖ)).obj P.obj := by
    simpa only [Functor.comp_obj, ObjectProperty.ι_obj] using
      (DerivedCategory.Plus.QCompιIso Cᵒᵖ).app P
  let e : E.functor.obj (objectOfBoundedAbove (C := C) K d) ≅
      (BoundedAboveDual.Q C).obj (BoundedAboveDual.ofBoundedAbove K d) :=
    (ObjectProperty.isoMk (DerivedCategory.TStructure.t (C := Cᵒᵖ)).plus
      (hRaw ≪≫ hPlus.symm)).op.symm
  exact E.inverse.mapIso e.symm ≪≫ (E.unitIso.app (objectOfBoundedAbove (C := C) K d)).symm

/-- Let C,D be abelian, F:C → D additive and D have a chosen derived
category. If K is zero above d, the derived object of the termwise
mapped complex F(K) lies in D⁻(D), with the same upper term bound. -/
def actualMappedObject (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    DerivedCategory.Minus D := by
  let _ : CochainComplex.IsStrictlyLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) d := by infer_instance
  exact objectOfBoundedAbove (C := D) ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) d

/-- Let C,D be abelian with independently chosen derived categories
for C,Cᵒᵖ,D,Dᵒᵖ, and F:C → D additive.
Write C_-=(CochainComplex.Plus(Cᵒᵖ))ᵒᵖ for the bounded-above
complex model, and Q_C:C_- → D⁻(C) for its localization. Assume C has enough projectives.
For K zero above d and with every K^n projective, the canonical
isomorphism LF([K]) ≅ [F(K)] in D⁻(D), retaining the original
termwise mapped complex. -/
def projectiveNativeComputationIso (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ n : ℤ, Projective (K.X n)] :
    (leftDerived F).obj (objectOfBoundedAbove (C := C) K d) ≅ actualMappedObject F K d := by
  let K' : CochainComplex D ℤ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let _ : CochainComplex.IsStrictlyLE K' d := by infer_instance
  let e : BoundedAboveDual.actualMappedComplex F K d ≅ BoundedAboveDual.ofBoundedAbove K' d :=
    eqToIso (by rfl)
  exact (leftDerived F).mapIso (nativeLocalizationIso (C := C) K d).symm ≪≫
    (localizationComputationIso F).app
      ((BoundedAboveDual.Q C).obj (BoundedAboveDual.ofBoundedAbove K d)) ≪≫
    (DerivedCategory.minusOppositeEquivalence D).inverse.mapIso
      (BoundedAboveDual.projectiveActualComplexIso F K d) ≪≫
    (Q D).mapIso e ≪≫ nativeLocalizationIso (C := D) K' d

end DerivedCategory.CanonicalLeft

end
