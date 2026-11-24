/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureCofibrant
public import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureFibrant
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Derived adjunctions of Quillen pairs

A Quillen adjunction induces an adjunction between its canonical total
derived functors on the localizations at the weak equivalences.  The two
composite derived-functor conditions are obtained from the cofibrant and
fibrant derivability structures; no absoluteness instance is assumed.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory MorphismProperty
open CategoryTheory.Functor

namespace HomotopicalAlgebra

/-- The canonical total derived functors of a Quillen adjunction, their
comparison maps, the four derived-functor proofs needed by
`CategoryTheory.Adjunction.derived`, and the resulting adjunction. -/
structure QuillenDerivedAdjunctionData
    {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) where
  /-- The actual total left derived functor between the two original localizations. -/
  leftDerived :
    (weakEquivalences C).Localization ⥤
      (weakEquivalences D).Localization
  /-- The total right derived functor back to the original source localization. -/
  rightDerived :
    (weakEquivalences D).Localization ⥤
      (weakEquivalences C).Localization
  /-- The complete original counit comparison from the chosen total left derived functor. -/
  leftComparison :
    (weakEquivalences C).Q ⋙ leftDerived ⟶
      L ⋙ (weakEquivalences D).Q
  /-- The original unit comparison into the complete chosen total right derived functor. -/
  rightComparison :
    R ⋙ (weakEquivalences C).Q ⟶
      (weakEquivalences D).Q ⋙ rightDerived
  leftIsDerived :
    leftDerived.IsLeftDerivedFunctor leftComparison
      (weakEquivalences C)
  rightIsDerived :
    rightDerived.IsRightDerivedFunctor rightComparison
      (weakEquivalences D)
  leftCompositeIsDerived :
    (leftDerived ⋙ rightDerived).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight leftComparison rightDerived)
      (weakEquivalences C)
  rightCompositeIsDerived :
    (rightDerived ⋙ leftDerived).IsRightDerivedFunctor
      (whiskerRight rightComparison leftDerived ≫
        (Functor.associator _ _ _).hom)
      (weakEquivalences D)
  /-- The actual adjunction between the two complete chosen total derived functors. -/
  adjunction : leftDerived ⊣ rightDerived

/-- The canonical adjunction between the total left and right derived
functors of a Quillen adjunction. -/
noncomputable def quillenDerivedAdjunctionData
    {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [CategoryTheory.Adjunction.IsQuillenAdjunction adj] :
    QuillenDerivedAdjunctionData adj := by
  let WC := weakEquivalences C
  let WD := weakEquivalences D
  let γC := WC.Q
  let γD := WD.Q
  let TL := L ⋙ γD
  let TR := R ⋙ γC
  let ΦC := CofibrantObject.localizerMorphism C
  let ΦD := FibrantObject.localizerMorphism D
  have hL : ΦC.Derives TL := by
    intro X Y f hf
    let _ : WeakEquivalence f.hom := by
      rw [← weakEquivalence_iff_of_objectProperty, weakEquivalence_iff]
      exact hf
    let _ : WeakEquivalence (L.map f.hom) :=
      Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
        (adj := adj) f.hom
    apply Localization.inverts γD WD
    change weakEquivalences D (L.map f.hom)
    rw [← weakEquivalence_iff]
    exact inferInstanceAs (WeakEquivalence (L.map f.hom))
  have hR : ΦD.Derives TR := by
    intro X Y f hf
    let _ : WeakEquivalence f.hom := by
      rw [← weakEquivalence_iff_of_objectProperty, weakEquivalence_iff]
      exact hf
    let _ : WeakEquivalence (R.map f.hom) :=
      Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
        (adj := adj) f.hom
    apply Localization.inverts γC WC
    change weakEquivalences C (R.map f.hom)
    rw [← weakEquivalence_iff]
    exact inferInstanceAs (WeakEquivalence (R.map f.hom))
  let _ : TL.HasPointwiseLeftDerivedFunctor WC :=
    hL.hasPointwiseLeftDerivedFunctor
  let _ : TR.HasPointwiseRightDerivedFunctor WD :=
    hR.hasPointwiseRightDerivedFunctor
  let LL := TL.totalLeftDerived γC WC
  let RR := TR.totalRightDerived γD WD
  let α := TL.totalLeftDerivedCounit γC WC
  let β := TR.totalRightDerivedUnit γD WD
  have hLL : LL.IsLeftDerivedFunctor α WC := inferInstance
  have hRR : RR.IsRightDerivedFunctor β WD := inferInstance
  let αLR := (Functor.associator γC LL RR).inv ≫ whiskerRight α RR
  let βRL := whiskerRight β LL ≫ (Functor.associator γD RR LL).hom
  have hLR : ΦC.Derives (TL ⋙ RR) := by
    intro X Y f hf
    let _ : IsIso (TL.map (ΦC.functor.map f)) := hL f hf
    dsimp
    exact Functor.map_isIso RR _
  have hRL : ΦD.Derives (TR ⋙ LL) := by
    intro X Y f hf
    let _ : IsIso (TR.map (ΦD.functor.map f)) := hR f hf
    dsimp
    exact Functor.map_isIso LL _
  have hαLR (X : CofibrantObject C) :
      IsIso (αLR.app (ΦC.functor.obj X)) := by
    have := hL.isIso' α X
    dsimp [αLR]
    infer_instance
  have hβRL (Y : FibrantObject D) :
      IsIso (βRL.app (ΦD.functor.obj Y)) := by
    have := hR.isIso_of_isRightDerivedFunctor β Y
    dsimp [βRL]
    infer_instance
  have hLLRR : (LL ⋙ RR).IsLeftDerivedFunctor αLR WC :=
    hLR.isLeftDerivedFunctor_of_isIso αLR hαLR
  have hRRLL : (RR ⋙ LL).IsRightDerivedFunctor βRL WD :=
    hRL.isRightDerivedFunctor_of_isIso βRL hβRL
  let _ : LL.IsLeftDerivedFunctor α WC := hLL
  let _ : RR.IsRightDerivedFunctor β WD := hRR
  let _ : (LL ⋙ RR).IsLeftDerivedFunctor αLR WC := hLLRR
  let _ : (RR ⋙ LL).IsRightDerivedFunctor βRL WD := hRRLL
  exact
    { leftDerived := LL
      rightDerived := RR
      leftComparison := α
      rightComparison := β
      leftIsDerived := hLL
      rightIsDerived := hRR
      leftCompositeIsDerived := hLLRR
      rightCompositeIsDerived := hRRLL
      adjunction := adj.derived WC WD α β }

end HomotopicalAlgebra
