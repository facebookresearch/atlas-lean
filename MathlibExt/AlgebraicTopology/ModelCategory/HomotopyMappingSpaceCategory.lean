/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel

/-!
# The actual monoidal category of homotopy mapping spaces

The chosen Kan--Quillen weak equivalences are preserved by the original
simplicial tensor products. Their actual localization therefore has the
localized monoidal structure and its original natural tensor comparisons.
This is the target category for coherent derived mapping enrichment.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v

open CategoryTheory MonoidalCategory MorphismProperty
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.HomotopyMappingSpaceCategory

/-- Every original simplicial set is cofibrant in the actual selected model. -/
theorem all_isCofibrant (X : SSet.{v}) : IsCofibrant X :=
  SSet.modelCategoryQuillen.cofibration_of_mono (Limits.initial.to X)

/-- The original closed tensor preserves initial objects in the scalar square. -/
def initialTensorSquare (K : SSet.{v}) {X Y : SSet.{v}} (f : X ⟶ Y) :
    (curriedTensor SSet.{v}).PushoutObjObj (Limits.initial.to K) f := by
  letI : Limits.PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    ((ihom.adjunction X).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight X)).leftAdjoint_preservesColimits
  letI : Limits.PreservesColimitsOfSize.{0, 0} (tensorRight Y) :=
    ((ihom.adjunction Y).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight Y)).leftAdjoint_preservesColimits
  exact Functor.PushoutObjObj.ofIsInitialLeft (curriedTensor SSet.{v})
    (Limits.initial.to K) f Limits.initialIsInitial

set_option backward.isDefEq.respectTransparency false in
/-- The same actual initial pushout-product arrow is the original tensor-map arrow. -/
def initialTensorArrowIso (K : SSet.{v}) {X Y : SSet.{v}} (f : X ⟶ Y) :
    Arrow.mk ((Arrow.mk (Limits.initial.to K) □ Arrow.mk f).hom) ≅ Arrow.mk (K ◁ f) := by
  let sq₁ : (curriedTensor SSet.{v}).PushoutObjObj (Limits.initial.to K) f :=
    Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) (Limits.initial.to K) f
  let sq₂ : (curriedTensor SSet.{v}).PushoutObjObj (Limits.initial.to K) f :=
    initialTensorSquare K f
  have e : Arrow.mk sq₁.ι ≅ Arrow.mk sq₂.ι :=
    Functor.PushoutObjObj.ι_iso_of_iso_left (f₁ := Arrow.mk (Limits.initial.to K))
      (f₁' := Arrow.mk (Limits.initial.to K)) (f₂ := Arrow.mk f) sq₁ sq₂ (Iso.refl _)
  exact e

/-- The actual closed tensor--Hom adjunction is Quillen from the original scalar PP laws. -/
theorem tensorAdjunction_isQuillen (K : SSet.{v}) :
    (ihom.adjunction K).IsQuillenAdjunction := by
  let _ : IsCofibrant K := all_isCofibrant K
  constructor
  · intro X Y f hf
    let _ : Cofibration f := (cofibration_iff _).mpr hf
    have hp : cofibrations SSet.{v} ((Arrow.mk (Limits.initial.to K) □ Arrow.mk f).hom) :=
      (cofibration_iff _).mp (SSet.cofibration_pushoutProduct (Limits.initial.to K) f)
    exact ((cofibrations SSet.{v}).arrow_mk_iso_iff (initialTensorArrowIso K f)).mp hp
  · intro X Y f hf
    let _ : Cofibration f := (cofibration_iff _).mpr hf.1
    let _ : WeakEquivalence f := (weakEquivalence_iff _).mpr hf.2
    have hp : trivialCofibrations SSet.{v}
        ((Arrow.mk (Limits.initial.to K) □ Arrow.mk f).hom) :=
      SSet.pushoutProduct_mem_trivialCofibrations_of_right (Limits.initial.to K) f
    exact ((trivialCofibrations SSet.{v}).arrow_mk_iso_iff (initialTensorArrowIso K f)).mp hp

/-- Original tensoring preserves realization weakness by the actual Quillen/Brown source theorem. -/
theorem tensor_whiskerLeft_weak (K : SSet.{v}) {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : SSet.realizationWeakEquivalences f) : SSet.realizationWeakEquivalences (K ◁ f) := by
  let _ : IsCofibrant X := all_isCofibrant X
  let _ : IsCofibrant Y := all_isCofibrant Y
  let _ : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  let _ : (ihom.adjunction K).IsQuillenAdjunction := tensorAdjunction_isQuillen K
  let _ : WeakEquivalence (K ◁ f) :=
    CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := ihom.adjunction K) f
  exact mem_weakEquivalences (K ◁ f)

/-- The original realization weak maps are monoidal by the actual source tensor preservation proof.
-/
instance realizationWeak_isMonoidal : (SSet.realizationWeakEquivalences.{v}).IsMonoidal where
  toIsMultiplicative := by
    change (weakEquivalences SSet.{v}).IsMultiplicative
    infer_instance
  whiskerLeft X _ _ f hf := tensor_whiskerLeft_weak X f hf
  whiskerRight {X Y} f hf Z := by
    have h : SSet.realizationWeakEquivalences (f ▷ Z) ↔
        SSet.realizationWeakEquivalences (Z ◁ f) :=
      SSet.realizationWeakEquivalences.arrow_mk_iso_iff
        (Arrow.isoMk (β_ X Z) (β_ Y Z)
          (BraidedCategory.braiding_naturality_left f Z).symm)
    exact h.mpr (tensor_whiskerLeft_weak Z f hf)

/-- The original localization of simplicial sets, with its actual constructed monoidal structure. -/
abbrev SpaceHo := LocalizedMonoidal (SSet.realizationWeakEquivalences.{v}.Q)
  SSet.realizationWeakEquivalences (Iso.refl
    (SSet.realizationWeakEquivalences.Q.obj (𝟙_ SSet.{v})))

/-- The actual original monoidal localization functor on all simplicial objects and maps. -/
abbrev localize : SSet.{v} ⥤ SpaceHo.{v} :=
  Localization.Monoidal.toMonoidalCategory SSet.realizationWeakEquivalences.Q
    SSet.realizationWeakEquivalences (Iso.refl _)

/-- Every original realization weak map becomes an isomorphism under the same localization. -/
theorem localize_isIso {X Y : SSet.{v}} (f : X ⟶ Y) (hf : SSet.realizationWeakEquivalences f) :
    IsIso (localize.map f) := Localization.inverts localize SSet.realizationWeakEquivalences f hf

/-- The localized tensor retains the natural comparison with the same original simplicial tensor. -/
def tensorComparison (X Y : SSet.{v}) :
    localize.obj X ⊗ localize.obj Y ≅ localize.obj (X ⊗ Y) :=
  Localization.Monoidal.μ SSet.realizationWeakEquivalences.Q SSet.realizationWeakEquivalences
    (Iso.refl _) X Y

/-- The tensor comparison retains every original source map. -/
theorem tensorComparison_naturality_left {X X' : SSet.{v}} (f : X ⟶ X') (Y : SSet.{v}) :
    localize.map f ▷ localize.obj Y ≫ (tensorComparison X' Y).hom =
      (tensorComparison X Y).hom ≫ localize.map (f ▷ Y) :=
  Localization.Monoidal.μ_natural_left _ _ _ f Y

/-- The tensor comparison retains every original target map. -/
theorem tensorComparison_naturality_right (X : SSet.{v}) {Y Y' : SSet.{v}} (f : Y ⟶ Y') :
    localize.obj X ◁ localize.map f ≫ (tensorComparison X Y').hom =
      (tensorComparison X Y).hom ≫ localize.map (X ◁ f) :=
  Localization.Monoidal.μ_natural_right _ _ _ X f

end HomotopicalAlgebra.HomotopyMappingSpaceCategory

end
end
end
