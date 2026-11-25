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
# The genuine left derived functor on canonical native Minus

The earned Minus/opposite-Plus equivalences transport the already proved
left-derived functor and its counit. Native derived-functor equivalence
transport proves the universal property for the canonical localization.
The projective computation is then expressed on the original native
Minus object of the actual original cochain complex.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.DerivedCategory Opposite

universe uC vC uD vD wC wCo wD wDo

namespace DerivedCategory.CanonicalLeft

variable (C : Type uC) [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wCo} Cᵒᵖ]

/-- The actual bounded-above complex localization into canonical native Minus. -/
def Q : BoundedAboveDual.Complex C ⥤ DerivedCategory.Minus C :=
  BoundedAboveDual.Q C ⋙ (DerivedCategory.minusOppositeEquivalence C).inverse

/-- The earned target equivalence preserves the original localization property. -/
instance localization : (Q C).IsLocalization (BoundedAboveDual.quasiIso C) :=
  Functor.IsLocalization.of_equivalence_target (BoundedAboveDual.Q C)
    (BoundedAboveDual.quasiIso C) (Q C) (DerivedCategory.minusOppositeEquivalence C).symm (Iso.refl _)

variable {C} {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wDo} Dᵒᵖ]
  [EnoughProjectives C] (F : C ⥤ D) [F.Additive]

/-- The actual additive cochain functor followed by canonical Minus localization. -/
def underived : BoundedAboveDual.Complex C ⥤ DerivedCategory.Minus D :=
  BoundedAboveDual.mapComplex F ⋙ Q D

/-- Native opposite derivation transported through the earned canonical Minus equivalences. -/
def leftDerived : DerivedCategory.Minus C ⥤ DerivedCategory.Minus D :=
  (DerivedCategory.minusOppositeEquivalence C).functor ⋙
    (BoundedAboveDual.leftDerived F ⋙ (DerivedCategory.minusOppositeEquivalence D).inverse)

/-- The proved opposite-Plus derivation with its target returned to canonical native Minus. -/
abbrev postDerived : BoundedAboveDual.Derived C ⥤ DerivedCategory.Minus D :=
  BoundedAboveDual.leftDerived F ⋙ (DerivedCategory.minusOppositeEquivalence D).inverse

/-- Canonical localization followed by the derived functor computes the original opposite-Plus derivation. -/
def localizationComputationIso :
    (DerivedCategory.minusOppositeEquivalence C).inverse ⋙ leftDerived F ≅ postDerived F :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.minusOppositeEquivalence C).counitIso (postDerived F) ≪≫
    Functor.leftUnitor _

/-- The genuine left-derived counit on the canonical native bounded-above localization. -/
def counit : Q C ⋙ leftDerived F ⟶ underived F :=
  (Functor.associator _ _ _).hom ≫
    (Functor.isoWhiskerLeft (BoundedAboveDual.Q C) (localizationComputationIso F)).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (BoundedAboveDual.counit F) (DerivedCategory.minusOppositeEquivalence D).inverse

/-- Equivalence transport gives the genuine left-derived universal property on canonical Minus. -/
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
      Functor.whiskerRight (BoundedAboveDual.counit F) (DerivedCategory.minusOppositeEquivalence D).inverse
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

/-- The original bounded-above cochain complex as its canonical native Minus object. -/
def objectOfBoundedAbove (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    DerivedCategory.Minus C :=
  { obj := DerivedCategory.Q.obj K
    property := ⟨d, inferInstance⟩ }

/-- The canonical localization model is identified with the actual native derived image of K. -/
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
    simpa only [Functor.comp_obj, ObjectProperty.ι_obj] using (DerivedCategory.Plus.QCompιIso Cᵒᵖ).app P
  let e : E.functor.obj (objectOfBoundedAbove (C := C) K d) ≅
      (BoundedAboveDual.Q C).obj (BoundedAboveDual.ofBoundedAbove K d) :=
    (ObjectProperty.isoMk (DerivedCategory.TStructure.t (C := Cᵒᵖ)).plus (hRaw ≪≫ hPlus.symm)).op.symm
  exact E.inverse.mapIso e.symm ≪≫ (E.unitIso.app (objectOfBoundedAbove (C := C) K d)).symm

/-- The actual original mapped complex as a canonical native Minus object. -/
def actualMappedObject (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    DerivedCategory.Minus D := by
  let _ : CochainComplex.IsStrictlyLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) d := by infer_instance
  exact objectOfBoundedAbove (C := D) ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) d

/-- The actual projective computation is now on native Minus objects, not an unproved alternate category. -/
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
