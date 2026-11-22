/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.SmallObject.ConstructionAccessibility
import MathlibExt.CategoryTheory.SmallObject.Iteration.Accessible
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.FactorArrowFunctors
import MathlibExt.CategoryTheory.NatTrans.PointwiseArrowPreservation
import MathlibExt.CategoryTheory.SmallObject.EndpointProfile
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
import Mathlib.CategoryTheory.Presentable.StrongGenerator

/-!
# Accessibility of the same original fixed-cardinal factors

The original one-step functor and pointed iteration remain at the supplied
small-object cardinal and ordinal bottom. Accessibility is proved at an
independently supplied compatible rank using both original endpoint bounds.
The middle functor and both existing factor Arrow functors keep every
original object, square map and factor map.
-/

set_option autoImplicit false
noncomputable section

universe w uC vC

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty HomotopicalAlgebra
open Cardinal

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type uC} [Category.{vC} C] {P Q : MorphismProperty C}

/-- Accessibility of the original middle implies accessibility of the SAME first factor Arrow. -/
theorem originalLeftFactorFunctor_isCardinalAccessible
    (B : FunctorialFactorizationData P Q) (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [HasCardinalFilteredColimits C χ] [B.Z.IsCardinalAccessible χ] :
    B.originalLeftFactorFunctor.IsCardinalAccessible χ := by
  let : (Arrow.leftFunc : Arrow C ⥤ C).IsCardinalAccessible χ :=
    inferInstanceAs (Functor.IsCardinalAccessible (Comma.fst (𝟭 C) (𝟭 C)) χ)
  change (NatTrans.arrow B.i).IsCardinalAccessible χ
  exact NatTrans.arrow_isCardinalAccessible B.i χ

/-- Accessibility of the original middle implies accessibility of the SAME second factor Arrow. -/
theorem originalRightFactorFunctor_isCardinalAccessible
    (B : FunctorialFactorizationData P Q) (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [HasCardinalFilteredColimits C χ] [B.Z.IsCardinalAccessible χ] :
    B.originalRightFactorFunctor.IsCardinalAccessible χ := by
  let : (Arrow.rightFunc : Arrow C ⥤ C).IsCardinalAccessible χ :=
    inferInstanceAs (Functor.IsCardinalAccessible (Comma.snd (𝟭 C) (𝟭 C)) χ)
  change (NatTrans.arrow B.p).IsCardinalAccessible χ
  exact NatTrans.arrow_isCardinalAccessible B.p χ

end CategoryTheory.MorphismProperty.FunctorialFactorizationData

namespace CategoryTheory.SmallObject

variable {C : Type uC} [Category.{vC} C] [HasColimitsOfSize.{w, w} C]
  (I : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [OrderBot κ.ord.ToType] [I.IsCardinalForSmallObjectArgument κ]
  (χ : Cardinal.{w}) [Fact χ.IsRegular]
  [∀ i : I.toSet, IsCardinalPresentable i.1.left χ]
  [∀ i : I.toSet, IsCardinalPresentable i.1.right χ]

/-- Both original endpoint bounds preserve the SAME original fixedκ iteration. -/
theorem iteration_isCardinalAccessible :
    (SmallObject.iteration I κ).IsCardinalAccessible χ := by
  let : MorphismProperty.IsSmall.{w} I := SmallObject.isSmall I κ
  let : LocallySmall.{w} C := SmallObject.locallySmall I κ
  let := hasIterationOfShape I κ
  let := hasColimitsOfShape_discrete I κ
  let := hasPushouts I κ
  let : (SmallObject.functor I.homFamily).IsCardinalAccessible χ :=
    functor_isCardinalAccessible I.homFamily χ
  change ((SuccStruct.ofNatTrans (ε I.homFamily)).iteration κ.ord.ToType).IsCardinalAccessible χ
  exact SuccStruct.isCardinalAccessible_iteration (ε I.homFamily) χ

/-- The original middle Z is the SAME κ-iteration followed by its original left projection. -/
theorem functorialFactorizationData_Z_isCardinalAccessible :
    (SmallObject.functorialFactorizationData I κ).Z.IsCardinalAccessible χ := by
  let : (SmallObject.iteration I κ).IsCardinalAccessible χ := iteration_isCardinalAccessible I κ χ
  let : (Arrow.leftFunc : Arrow C ⥤ C).IsCardinalAccessible χ :=
    inferInstanceAs (Functor.IsCardinalAccessible (Comma.fst (𝟭 C) (𝟭 C)) χ)
  change (SmallObject.iteration I κ ⋙ Arrow.leftFunc).IsCardinalAccessible χ
  infer_instance

/-- The SAME original fixedκ first-factor Arrow functor is accessible. -/
theorem functorialFactorizationData_left_isCardinalAccessible :
    (SmallObject.functorialFactorizationData I κ).originalLeftFactorFunctor.IsCardinalAccessible
      χ := by
  let : (SmallObject.functorialFactorizationData I κ).Z.IsCardinalAccessible χ :=
    functorialFactorizationData_Z_isCardinalAccessible I κ χ
  exact (SmallObject.functorialFactorizationData I κ).originalLeftFactorFunctor_isCardinalAccessible
    χ

/-- The SAME original fixedκ second-factor Arrow functor is accessible. -/
theorem functorialFactorizationData_right_isCardinalAccessible :
    (SmallObject.functorialFactorizationData I κ).originalRightFactorFunctor.IsCardinalAccessible
      χ := by
  let : (SmallObject.functorialFactorizationData I κ).Z.IsCardinalAccessible χ :=
    functorialFactorizationData_Z_isCardinalAccessible I κ χ
  exact
    (SmallObject.functorialFactorizationData I κ).originalRightFactorFunctor_isCardinalAccessible χ

end CategoryTheory.SmallObject

namespace HomotopicalAlgebra.CofibrantGenerationData

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

section FixedRank

variable [HasColimitsOfSize.{w, w} C] (d : CofibrantGenerationData C κ)
  (χ : Cardinal.{w}) [Fact χ.IsRegular]

/-- The actual I middle getter preserves χ-filtered colimits using both original endpoints. -/
theorem cofibrantFactorizationData_Z_isCardinalAccessible
    [∀ i : d.I.toSet, IsCardinalPresentable i.1.left χ]
    [∀ i : d.I.toSet, IsCardinalPresentable i.1.right χ] :
    d.cofibrantFactorizationData.Z.IsCardinalAccessible χ := by
  let : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  change (SmallObject.functorialFactorizationData d.I κ).Z.IsCardinalAccessible χ
  exact SmallObject.functorialFactorizationData_Z_isCardinalAccessible d.I κ χ

/-- The actual J middle getter uses the same original κ and both J endpoint bounds. -/
theorem fibrantFactorizationData_Z_isCardinalAccessible
    [∀ i : d.J.toSet, IsCardinalPresentable i.1.left χ]
    [∀ i : d.J.toSet, IsCardinalPresentable i.1.right χ] :
    d.fibrantFactorizationData.Z.IsCardinalAccessible χ := by
  let : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
  change (SmallObject.functorialFactorizationData d.J κ).Z.IsCardinalAccessible χ
  exact SmallObject.functorialFactorizationData_Z_isCardinalAccessible d.J κ χ

/-- Accessibility of the actual I first factor, retaining its original i and square maps. -/
theorem cofibrantFactorizationData_left_isCardinalAccessible
    [∀ i : d.I.toSet, IsCardinalPresentable i.1.left χ]
    [∀ i : d.I.toSet, IsCardinalPresentable i.1.right χ] :
    d.cofibrantFactorizationData.originalLeftFactorFunctor.IsCardinalAccessible χ := by
  let : d.cofibrantFactorizationData.Z.IsCardinalAccessible χ :=
    d.cofibrantFactorizationData_Z_isCardinalAccessible χ
  exact d.cofibrantFactorizationData.originalLeftFactorFunctor_isCardinalAccessible χ

/-- Accessibility of the actual I second factor, retaining its original p and square maps. -/
theorem cofibrantFactorizationData_right_isCardinalAccessible
    [∀ i : d.I.toSet, IsCardinalPresentable i.1.left χ]
    [∀ i : d.I.toSet, IsCardinalPresentable i.1.right χ] :
    d.cofibrantFactorizationData.originalRightFactorFunctor.IsCardinalAccessible χ := by
  let : d.cofibrantFactorizationData.Z.IsCardinalAccessible χ :=
    d.cofibrantFactorizationData_Z_isCardinalAccessible χ
  exact d.cofibrantFactorizationData.originalRightFactorFunctor_isCardinalAccessible χ

/-- Accessibility of the actual J first factor with its unchanged original inclusion. -/
theorem fibrantFactorizationData_left_isCardinalAccessible
    [∀ i : d.J.toSet, IsCardinalPresentable i.1.left χ]
    [∀ i : d.J.toSet, IsCardinalPresentable i.1.right χ] :
    d.fibrantFactorizationData.originalLeftFactorFunctor.IsCardinalAccessible χ := by
  let : d.fibrantFactorizationData.Z.IsCardinalAccessible χ :=
    d.fibrantFactorizationData_Z_isCardinalAccessible χ
  exact d.fibrantFactorizationData.originalLeftFactorFunctor_isCardinalAccessible χ

/-- Accessibility of the actual J second factor with its unchanged original projection. -/
theorem fibrantFactorizationData_right_isCardinalAccessible
    [∀ i : d.J.toSet, IsCardinalPresentable i.1.left χ]
    [∀ i : d.J.toSet, IsCardinalPresentable i.1.right χ] :
    d.fibrantFactorizationData.originalRightFactorFunctor.IsCardinalAccessible χ := by
  let : d.fibrantFactorizationData.Z.IsCardinalAccessible χ :=
    d.fibrantFactorizationData_Z_isCardinalAccessible χ
  exact d.fibrantFactorizationData.originalRightFactorFunctor_isCardinalAccessible χ

end FixedRank

/-- A compatible common rank for both SAME original fixedκ factorizations. The
LP rank, SOA length and accessibility rank are independently quantified; only
the original endpoint objects and the base LP property are enlarged. -/
theorem exists_common_factor_accessibility_cardinal
    (d : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    ∃ (χ : Cardinal.{w}) (hχ : Fact χ.IsRegular),
      letI : Fact χ.IsRegular := hχ
      ℵ₀ < χ ∧ κLP ≤ χ ∧ κ ≤ χ ∧ IsCardinalLocallyPresentable C χ ∧
        (∀ i : d.I.toSet,
          IsCardinalPresentable i.1.left χ ∧ IsCardinalPresentable i.1.right χ) ∧
        (∀ j : d.J.toSet,
          IsCardinalPresentable j.1.left χ ∧ IsCardinalPresentable j.1.right χ) ∧
        d.cofibrantFactorizationData.Z.IsCardinalAccessible χ ∧
        d.fibrantFactorizationData.Z.IsCardinalAccessible χ ∧
        d.cofibrantFactorizationData.originalLeftFactorFunctor.IsCardinalAccessible χ ∧
        d.cofibrantFactorizationData.originalRightFactorFunctor.IsCardinalAccessible χ ∧
        d.fibrantFactorizationData.originalLeftFactorFunctor.IsCardinalAccessible χ ∧
        d.fibrantFactorizationData.originalRightFactorFunctor.IsCardinalAccessible χ := by
  let : IsAccessibleCategory.{w} C := ⟨κLP, inferInstance, inferInstance⟩
  let : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  let : d.J.IsCardinalForSmallObjectArgument κ := d.J_smallObject
  let Fixed := κLP.ord.ToType ⊕ κ.ord.ToType
  obtain ⟨μI, hRegularI, hωI, hFixedI, hEndpointsI⟩ :=
    SmallObject.original_endpoints_have_common_presentability_cardinal d.I κ Fixed
  obtain ⟨μJ, hRegularJ, _hωJ, _hFixedJ, hEndpointsJ⟩ :=
    SmallObject.original_endpoints_have_common_presentability_cardinal d.J κ Fixed
  let : Fact μI.IsRegular := hRegularI
  let : Fact μJ.IsRegular := hRegularJ
  let Upper := μI.ord.ToType ⊕ μJ.ord.ToType
  obtain ⟨χ, hRegular, hUpper⟩ := HasCardinalLT.exists_regular_cardinal Upper
  let : Fact χ.IsRegular := ⟨hRegular⟩
  have hμI : μI < χ := by
    have h := hUpper.of_injective (Sum.inl : μI.ord.ToType → Upper) Sum.inl_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hμJ : μJ < χ := by
    have h := hUpper.of_injective (Sum.inr : μJ.ord.ToType → Upper) Sum.inr_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hFixed : HasCardinalLT Fixed χ := hFixedI.of_le hμI.le
  have hLP : κLP < χ := by
    have h := hFixed.of_injective (Sum.inl : κLP.ord.ToType → Fixed) Sum.inl_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hκ : κ < χ := by
    have h := hFixed.of_injective (Sum.inr : κ.ord.ToType → Fixed) Sum.inr_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hI (i : d.I.toSet) :
      IsCardinalPresentable i.1.left χ ∧ IsCardinalPresentable i.1.right χ := by
    let : IsCardinalPresentable i.1.left μI := (hEndpointsI i).1
    let : IsCardinalPresentable i.1.right μI := (hEndpointsI i).2
    exact ⟨isCardinalPresentable_of_le _ hμI.le, isCardinalPresentable_of_le _ hμI.le⟩
  have hJ (j : d.J.toSet) :
      IsCardinalPresentable j.1.left χ ∧ IsCardinalPresentable j.1.right χ := by
    let : IsCardinalPresentable j.1.left μJ := (hEndpointsJ j).1
    let : IsCardinalPresentable j.1.right μJ := (hEndpointsJ j).2
    exact ⟨isCardinalPresentable_of_le _ hμJ.le, isCardinalPresentable_of_le _ hμJ.le⟩
  let : ∀ i : d.I.toSet, IsCardinalPresentable i.1.left χ := fun i ↦ (hI i).1
  let : ∀ i : d.I.toSet, IsCardinalPresentable i.1.right χ := fun i ↦ (hI i).2
  let : ∀ j : d.J.toSet, IsCardinalPresentable j.1.left χ := fun j ↦ (hJ j).1
  let : ∀ j : d.J.toSet, IsCardinalPresentable j.1.right χ := fun j ↦ (hJ j).2
  exact ⟨χ, inferInstance, hωI.trans hμI, hLP.le, hκ.le,
    IsCardinalLocallyPresentable.of_le C hLP.le, hI, hJ,
    d.cofibrantFactorizationData_Z_isCardinalAccessible χ,
    d.fibrantFactorizationData_Z_isCardinalAccessible χ,
    d.cofibrantFactorizationData_left_isCardinalAccessible χ,
    d.cofibrantFactorizationData_right_isCardinalAccessible χ,
    d.fibrantFactorizationData_left_isCardinalAccessible χ,
    d.fibrantFactorizationData_right_isCardinalAccessible χ⟩

end HomotopicalAlgebra.CofibrantGenerationData
