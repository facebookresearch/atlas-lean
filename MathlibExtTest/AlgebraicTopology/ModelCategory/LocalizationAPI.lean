/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.SmithExistence
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.CombinatorialQuillenDescent

/-!
# Generic left Bousfield localization

Smith recognition constructs a model from closure and solution-set
hypotheses. For an empty family of localizing maps, the resulting
localization recovers the original weak equivalences and fibrant objects.
Quillen descent constructs the source localization from compatible
simplicial mapping data and local presentability, and descends an existing
Quillen adjunction when its derived functor inverts the localizing maps.
-/

set_option autoImplicit false
noncomputable section

universe w wS u v uD vD

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace AtlasModelCategoryTests.LocalizationAPI

section Smith

variable {C : Type u} [Category.{v} C]
  [HasFiniteLimits C] [HasFiniteColimits C] [IsLocallyPresentable.{w} C]

/-- Smith recognition constructs the model with all five morphism classes
and both weak factorization systems. -/
theorem smith_input_constructs_model
    (I W : MorphismProperty C) [I.HasSmallObjectArgument.{w}]
    (h : SmithRecognitionInput.{w} I W) :
    ∃ M : SmithModelStructureData.{w} I W,
      ∃ m : ModelCategory C,
        letI : ModelCategory C := m
        weakEquivalences C = W ∧
          cofibrations C = I.rlp.llp ∧
          fibrations C = M.J.rlp ∧
          trivialFibrations C = I.rlp ∧
          trivialCofibrations C = I.rlp.llp ⊓ W ∧
          M.J.rlp = (I.rlp.llp ⊓ W).rlp ∧
          IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C) ∧
          IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C) := by
  obtain ⟨M⟩ := smithRecognition I W h
  letI : CategoryWithCofibrations C := ⟨I.rlp.llp⟩
  letI : CategoryWithFibrations C := ⟨M.J.rlp⟩
  letI : CategoryWithWeakEquivalences C := ⟨W⟩
  let m := M.modelCategory h.weak_two_out_of_three rfl rfl rfl
  refine ⟨M, m, ?_⟩
  letI : ModelCategory C := m
  refine ⟨rfl, rfl, rfl, ?_, rfl, M.fibrations_eq, inferInstance, inferInstance⟩
  change M.J.rlp ⊓ W = I.rlp
  exact M.trivialFibrations_eq

end Smith

section EmptyFamily

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]
  [IsLocallyPresentable.{w} C]

/-- The empty-family model is obtained through Smith existence and then
recovers the original weak class, fibrant objects and Quillen equivalence. -/
theorem empty_localization_from_smith
    (sm : SimplicialModelCategoryData (C := C))
    (data : HomotopyFunctionComplexData (C := C))
    (calculus : HomotopyFunctionComplexCalculusData (C := C))
    {K : Type w} [IsEmpty K] (S : K → Arrow C)
    (I : MorphismProperty C) [I.HasSmallObjectArgument.{w}]
    (hI : I.rlp = trivialFibrations C)
    (hSmith : SmithRecognitionInput.{w} I (localEquivalences S)) :
    ∃ L : LeftBousfieldLocalizationData S,
      weakEquivalences (LeftLocalized L) =
          (weakEquivalences C).inverseImage (LeftLocalized.toBase L) ∧
        trivialFibrations (LeftLocalized L) =
          (trivialFibrations C).inverseImage (LeftLocalized.toBase L) ∧
        (∀ X : LeftLocalized L, IsFibrant X ↔ IsFibrant X.1) ∧
        Adjunction.IsQuillenEquivalence
          (LeftLocalized.emptyEquivalence L data).toAdjunction := by
  obtain ⟨L⟩ := leftBousfieldLocalizationDataOfSmith sm
    data.toHomotopyFunctionComplexInvarianceData.toHomotopyFunctionComplexPrecompData
    calculus S I hI hSmith
  refine ⟨L, ?_, LeftLocalized.trivialFibrations_eq L, ?_,
    LeftLocalized.empty_isQuillenEquivalence L data⟩
  · change (localEquivalences S).inverseImage (LeftLocalized.toBase L) = _
    rw [localEquivalences_empty data S]
  · intro X
    rw [LeftLocalized.fibrant_iff L X]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, fun k => isEmptyElim k⟩

end EmptyFamily

section BareTarget

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  [IsLeftProper C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (a : CompatibleSimplicialMapping.Action C)
  {K : Type wS} [Small.{w} K] (S : K → Arrow C)
  (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [adj.IsQuillenAdjunction]

/-- Source construction and all derived S-images give bare-target descent,
retaining both adjoint maps and the source trivial-fibration class. -/
theorem source_localization_descends_to_bare_target
    (hS : ∀ k, IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map
      ((weakEquivalences C).Q.map (S k).hom))) :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    let L := CombinatorialSourceRecognition.localizationData d a S κLP
    (CombinatorialQuillenDescent.adjunction d a S κLP adj).IsQuillenAdjunction ∧
      (∀ Z : D, IsFibrant Z → isLocalFibrant S (G.obj Z)) ∧
      (∀ X : CombinatorialEnrichment.Localized d a S κLP,
        ((CombinatorialQuillenDescent.adjunction d a S κLP adj).unit.app X).hom =
          adj.unit.app X.1) ∧
      (∀ Z : D,
        (CombinatorialQuillenDescent.adjunction d a S κLP adj).counit.app Z =
          adj.counit.app Z) ∧
      trivialFibrations (CombinatorialEnrichment.Localized d a S κLP) =
        (trivialFibrations C).inverseImage (LeftLocalized.toBase L) := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  refine ⟨CombinatorialQuillenDescent.isQuillenAdjunction d a S κLP adj hS,
    ?_, ?_, ?_, LeftLocalized.trivialFibrations_eq
      (CombinatorialSourceRecognition.localizationData d a S κLP)⟩
  · intro Z hZ
    letI : IsFibrant Z := hZ
    exact CombinatorialQuillenDescent.right_localFibrant d a S adj hS Z
  · intro X
    exact CombinatorialQuillenDescent.adjunction_unit d a S κLP adj X
  · intro Z
    exact CombinatorialQuillenDescent.adjunction_counit d a S κLP adj Z

end BareTarget

end AtlasModelCategoryTests.LocalizationAPI
