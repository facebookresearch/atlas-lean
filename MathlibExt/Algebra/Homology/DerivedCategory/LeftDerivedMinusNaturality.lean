/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.DerivedCategory.LeftDerivedMinus
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Natural transformations of canonical left derived functors on Minus

Use the native right-derived transformation of the opposite original
transformation, then return through the earned opposite/Minus equivalences.
The actual native counit square, identity, and composition laws transport
with the same maps. No naturality or derived-map certificate is input.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.DerivedCategory Opposite

universe uC vC uD vD wC wCo wD wDo

namespace DerivedCategory.CanonicalLeft.Naturality

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wCo} Cᵒᵖ]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wDo} Dᵒᵖ]
  [EnoughProjectives C]
  {F₁ F₂ F₃ : C ⥤ D} [F₁.Additive] [F₂.Additive] [F₃.Additive]

/-- The original cochain transformation in the native bounded-above opposite model. -/
def dualMapComplex (τ : F₁ ⟶ F₂) : BoundedAboveDual.mapComplex F₁ ⟶ BoundedAboveDual.mapComplex F₂ :=
  NatTrans.op (NatTrans.mapCochainComplexPlus (NatTrans.op τ))

/-- The actual right-derived opposite transformation gives the left-derived map. -/
def dualLeftDerived (τ : F₁ ⟶ F₂) : BoundedAboveDual.leftDerived F₁ ⟶ BoundedAboveDual.leftDerived F₂ :=
  NatTrans.op (NatTrans.rightDerivedFunctorPlus (NatTrans.op τ))

/-- Return the same actual transformation to canonical native Minus. -/
def lift (τ : F₁ ⟶ F₂) : CanonicalLeft.leftDerived F₁ ⟶ CanonicalLeft.leftDerived F₂ :=
  Functor.whiskerLeft (DerivedCategory.minusOppositeEquivalence C).functor
    (Functor.whiskerRight (dualLeftDerived τ) (DerivedCategory.minusOppositeEquivalence D).inverse)

/-- The original cochain map followed by canonical localization. -/
def underivedMap (τ : F₁ ⟶ F₂) : CanonicalLeft.underived F₁ ⟶ CanonicalLeft.underived F₂ :=
  Functor.whiskerRight (dualMapComplex τ) (CanonicalLeft.Q D)

@[simp]
theorem dualLeftDerived_id (F : C ⥤ D) [F.Additive] : dualLeftDerived (𝟙 F) = 𝟙 _ := by
  simp only [dualLeftDerived, NatTrans.op_id, NatTrans.rightDerivedFunctorPlus_id]
  rfl

theorem dualLeftDerived_comp (τ : F₁ ⟶ F₂) (σ : F₂ ⟶ F₃) :
    dualLeftDerived (τ ≫ σ) = dualLeftDerived τ ≫ dualLeftDerived σ := by
  simp only [dualLeftDerived, NatTrans.op_comp, NatTrans.rightDerivedFunctorPlus_comp]
  rfl

@[simp]
theorem lift_id (F : C ⥤ D) [F.Additive] : lift (𝟙 F) = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  change (DerivedCategory.minusOppositeEquivalence D).inverse.map
    ((dualLeftDerived (𝟙 F)).app ((DerivedCategory.minusOppositeEquivalence C).functor.obj X)) = _
  rw [dualLeftDerived_id]
  exact (DerivedCategory.minusOppositeEquivalence D).inverse.map_id _

theorem lift_comp (τ : F₁ ⟶ F₂) (σ : F₂ ⟶ F₃) : lift (τ ≫ σ) = lift τ ≫ lift σ := by
  apply NatTrans.ext
  funext X
  change (DerivedCategory.minusOppositeEquivalence D).inverse.map
      ((dualLeftDerived (τ ≫ σ)).app ((DerivedCategory.minusOppositeEquivalence C).functor.obj X)) = _
  rw [dualLeftDerived_comp]
  exact (DerivedCategory.minusOppositeEquivalence D).inverse.map_comp _ _

@[simp]
theorem underivedMap_id (F : C ⥤ D) [F.Additive] : underivedMap (𝟙 F) = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  change (CanonicalLeft.Q D).map ((dualMapComplex (𝟙 F)).app X) = _
  simp only [dualMapComplex, NatTrans.op_id, NatTrans.mapCochainComplexPlus_id]
  exact (CanonicalLeft.Q D).map_id _

theorem underivedMap_comp (τ : F₁ ⟶ F₂) (σ : F₂ ⟶ F₃) :
    underivedMap (τ ≫ σ) = underivedMap τ ≫ underivedMap σ := by
  apply NatTrans.ext
  funext X
  change (CanonicalLeft.Q D).map ((dualMapComplex (τ ≫ σ)).app X) =
    (CanonicalLeft.Q D).map ((dualMapComplex τ).app X) ≫
      (CanonicalLeft.Q D).map ((dualMapComplex σ).app X)
  simp only [dualMapComplex, NatTrans.op_comp, NatTrans.mapCochainComplexPlus_comp]
  exact (CanonicalLeft.Q D).map_comp _ _

/-- The native right-derived counit square is reflected with its exact original cochain transformation. -/
theorem dualCounit_square (τ : F₁ ⟶ F₂) :
    Functor.whiskerLeft (BoundedAboveDual.Q C) (dualLeftDerived τ) ≫ BoundedAboveDual.counit F₂ =
      BoundedAboveDual.counit F₁ ≫ Functor.whiskerRight (dualMapComplex τ) (BoundedAboveDual.Q D) := by
  apply NatTrans.ext
  funext X
  apply Quiver.Hom.unop_inj
  exact NatTrans.rightDerivedFunctorPlus_fac_app (NatTrans.op τ) (unop X)

/-- The source-equivalence comparison has exactly its native counit-map component. -/
theorem localization_hom_app (F : C ⥤ D) [F.Additive] (Y : BoundedAboveDual.Derived C) :
    (CanonicalLeft.localizationComputationIso F).hom.app Y =
      (CanonicalLeft.postDerived F).map ((DerivedCategory.minusOppositeEquivalence C).counitIso.hom.app Y) := by
  change 𝟙 _ ≫ (CanonicalLeft.postDerived F).map
    ((DerivedCategory.minusOppositeEquivalence C).counitIso.hom.app Y) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- The actual source-equivalence comparison is natural in the original additive-functor transformation. -/
theorem localization_lift (τ : F₁ ⟶ F₂) :
    Functor.whiskerLeft (DerivedCategory.minusOppositeEquivalence C).inverse (lift τ) ≫
        (CanonicalLeft.localizationComputationIso F₂).hom =
      (CanonicalLeft.localizationComputationIso F₁).hom ≫
        Functor.whiskerRight (dualLeftDerived τ) (DerivedCategory.minusOppositeEquivalence D).inverse := by
  apply NatTrans.ext
  funext Y
  change (lift τ).app ((DerivedCategory.minusOppositeEquivalence C).inverse.obj Y) ≫
      (CanonicalLeft.localizationComputationIso F₂).hom.app Y =
    (CanonicalLeft.localizationComputationIso F₁).hom.app Y ≫
      (DerivedCategory.minusOppositeEquivalence D).inverse.map ((dualLeftDerived τ).app Y)
  rw [localization_hom_app F₁, localization_hom_app F₂]
  exact ((Functor.whiskerRight (dualLeftDerived τ) (DerivedCategory.minusOppositeEquivalence D).inverse).naturality
    ((DerivedCategory.minusOppositeEquivalence C).counitIso.hom.app Y)).symm

/-- Canonical counit evaluation retains the same original opposite-derived component. -/
theorem counit_app (F : C ⥤ D) [F.Additive] (X : BoundedAboveDual.Complex C) :
    (CanonicalLeft.counit F).app X =
      (CanonicalLeft.localizationComputationIso F).hom.app ((BoundedAboveDual.Q C).obj X) ≫
        (DerivedCategory.minusOppositeEquivalence D).inverse.map ((BoundedAboveDual.counit F).app X) := by
  change 𝟙 _ ≫ (CanonicalLeft.localizationComputationIso F).hom.app
    ((BoundedAboveDual.Q C).obj X) ≫ 𝟙 _ ≫
      (DerivedCategory.minusOppositeEquivalence D).inverse.map ((BoundedAboveDual.counit F).app X) = _
  simp only [Category.id_comp]

/-- The actual canonical left-derived counit square on each original bounded-above complex. -/
theorem counit_square_app (τ : F₁ ⟶ F₂) (X : BoundedAboveDual.Complex C) :
    (lift τ).app ((CanonicalLeft.Q C).obj X) ≫ (CanonicalLeft.counit F₂).app X =
      (CanonicalLeft.counit F₁).app X ≫ (underivedMap τ).app X := by
  let G := (DerivedCategory.minusOppositeEquivalence D).inverse
  let Y := (BoundedAboveDual.Q C).obj X
  have hχ :
      (lift τ).app ((DerivedCategory.minusOppositeEquivalence C).inverse.obj Y) ≫
          (CanonicalLeft.localizationComputationIso F₂).hom.app Y =
        (CanonicalLeft.localizationComputationIso F₁).hom.app Y ≫
          G.map ((dualLeftDerived τ).app Y) :=
    NatTrans.congr_app (localization_lift τ) Y
  have hδ :
      (dualLeftDerived τ).app Y ≫ (BoundedAboveDual.counit F₂).app X =
        (BoundedAboveDual.counit F₁).app X ≫
          (BoundedAboveDual.Q D).map ((dualMapComplex τ).app X) :=
    NatTrans.congr_app (dualCounit_square τ) X
  rw [counit_app F₁, counit_app F₂]
  change (lift τ).app ((DerivedCategory.minusOppositeEquivalence C).inverse.obj Y) ≫
      ((CanonicalLeft.localizationComputationIso F₂).hom.app Y ≫
        G.map ((BoundedAboveDual.counit F₂).app X)) =
    ((CanonicalLeft.localizationComputationIso F₁).hom.app Y ≫
      G.map ((BoundedAboveDual.counit F₁).app X)) ≫
        G.map ((BoundedAboveDual.Q D).map ((dualMapComplex τ).app X))
  rw [← Category.assoc, hχ, Category.assoc, ← G.map_comp, hδ, G.map_comp]
  exact (Category.assoc _ _ _).symm

/-- The canonical counit square is a conclusion for every original additive natural transformation. -/
theorem counit_square (τ : F₁ ⟶ F₂) :
    Functor.whiskerLeft (CanonicalLeft.Q C) (lift τ) ≫ CanonicalLeft.counit F₂ =
      CanonicalLeft.counit F₁ ≫ underivedMap τ := by
  apply NatTrans.ext
  funext X
  exact counit_square_app τ X

/-- An original natural isomorphism induces the actual canonical derived natural isomorphism. -/
def liftIso (e : F₁ ≅ F₂) : CanonicalLeft.leftDerived F₁ ≅ CanonicalLeft.leftDerived F₂ where
  hom := lift e.hom
  inv := lift e.inv
  hom_inv_id := by rw [← lift_comp, e.hom_inv_id, lift_id]
  inv_hom_id := by rw [← lift_comp, e.inv_hom_id, lift_id]

end DerivedCategory.CanonicalLeft.Naturality

end
