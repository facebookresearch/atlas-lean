/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModelAtCardinal
import MathlibExt.CategoryTheory.SmallObject.CardinalPresentableSources

/-!
# Generation API integration

Source presentability supplies fixed-cardinal small-object constructions.
A common regular cardinal synchronizes two supplied families with local
presentability. Two-family recognition then constructs a model whose
right classes and complete factor maps retain those original families.
The tests include arbitrary Arrow maps, so naturality is checked alongside
factor membership and composition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe w u v t

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.GenerationAPI

section PresentableSources

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w,w} C]
  [LocallySmall.{w} C] {ι : Type t} [Small.{w} ι] {A B : ι → C}
  (f : ∀ i, A i ⟶ B i) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [∀ i, IsCardinalPresentable (A i) κ]

-- The fixed-rank source theorem produces an actual factor of every original arrow.
example (a : Arrow C) :
    let d := (ofHomsFunctorialFactorizationAtCardinal f κ).factorizationData a.hom
    (ofHoms f).rlp.llp d.i ∧ (ofHoms f).rlp d.p ∧ d.i ≫ d.p = a.hom := by
  let d := (ofHomsFunctorialFactorizationAtCardinal f κ).factorizationData a.hom
  exact ⟨d.hi, d.hp, d.fac⟩

-- The same supplied source law verifies the full small-object argument.
include κ in
example : HasSmallObjectArgument.{w} (ofHoms f) :=
  ofHoms_hasSmallObjectArgument_atCardinal f κ

end PresentableSources

section TwoFamilyRecognition

variable {C : Type u} [Category.{v} C] (I J W : MorphismProperty C)
  [I.HasSmallObjectArgument.{w}] [J.HasSmallObjectArgument.{w}]
  (hW : W.HasTwoOutOfThreeProperty) (hRight : I.rlp = J.rlp ⊓ W)
  (hAcyclic : J.rlp.llp ≤ W)

-- Recognition derives the acyclic left class and both right-class comparisons.
include hW hRight hAcyclic in
example : J.rlp.llp = I.rlp.llp ⊓ W ∧
    J.rlp = (I.rlp.llp ⊓ W).rlp ∧ J.rlp ⊓ W = I.rlp := by
  let d := SmithModelStructureData.ofGenerators I J W hW hRight hAcyclic
  exact ⟨d.trivialCofibrations_eq, d.fibrations_eq, d.trivialFibrations_eq⟩

-- Both weak factorization systems are obtained before constructing a model category.
include hW hRight hAcyclic in
example : IsWeakFactorizationSystem I.rlp.llp I.rlp ∧
    IsWeakFactorizationSystem J.rlp.llp J.rlp := by
  let d := SmithModelStructureData.ofGenerators I J W hW hRight hAcyclic
  exact ⟨d.cofibration_wfs, d.trivialCofibration_wfs⟩

end TwoFamilyRecognition

section SolutionSetRecognition

variable {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
  (I W : MorphismProperty C) [I.HasSmallObjectArgument.{w}]

-- Beke--Smith produces the other generating family from its generatorwise solution sets.
example (h : SmithRecognitionInput.{w} I W) :
    ∃ J : MorphismProperty C, J.HasSmallObjectArgument.{w} ∧
      IsWeakFactorizationSystem I.rlp.llp I.rlp ∧
      IsWeakFactorizationSystem J.rlp.llp J.rlp ∧
      J.rlp.llp = I.rlp.llp ⊓ W ∧ J.rlp = (I.rlp.llp ⊓ W).rlp ∧
      J.rlp ⊓ W = I.rlp := by
  obtain ⟨d⟩ := smithRecognition I W h
  exact ⟨d.J, d.J_smallObject, d.cofibration_wfs, d.trivialCofibration_wfs,
    d.trivialCofibrations_eq, d.fibrations_eq, d.trivialFibrations_eq⟩

end SolutionSetRecognition

section FixedCardinalRecognition

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] [HasFiniteColimits C]
  (I J W : MorphismProperty C) (κ : Cardinal.{w})
  [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ] [J.IsCardinalForSmallObjectArgument κ]
  (hW : W.HasTwoOutOfThreeProperty) (hRight : I.rlp = J.rlp ⊓ W)
  (hAcyclic : J.rlp.llp ≤ W)

-- The constructed model identifies both right classes from the supplied comparison.
example :
    letI : ModelCategory C :=
      OriginalGeneratedModelAtCardinal.modelCategory I J W κ hW hRight hAcyclic
    I.rlp = trivialFibrations C ∧ J.rlp = fibrations C := by
  letI : ModelCategory C :=
    OriginalGeneratedModelAtCardinal.modelCategory I J W κ hW hRight hAcyclic
  have h := OriginalGeneratedModelAtCardinal.five_classes I J W κ hW hRight hAcyclic
  exact ⟨h.2.2.2.2.symm, h.2.2.1.symm⟩

-- Both actual fixed-rank factor records retain their appropriate derived model classes.
example (a : Arrow C) :
    letI : ModelCategory C :=
      OriginalGeneratedModelAtCardinal.modelCategory I J W κ hW hRight hAcyclic
    let dI := (OriginalGeneratedModelAtCardinal.cofibrantFactorizationData
      I J W κ hW hRight hAcyclic).factorizationData a.hom
    let dJ := (OriginalGeneratedModelAtCardinal.fibrantFactorizationData
      I J W κ hW hRight hAcyclic).factorizationData a.hom
    cofibrations C dI.i ∧ trivialFibrations C dI.p ∧ dI.i ≫ dI.p = a.hom ∧
      trivialCofibrations C dJ.i ∧ fibrations C dJ.p ∧ dJ.i ≫ dJ.p = a.hom := by
  letI : ModelCategory C :=
    OriginalGeneratedModelAtCardinal.modelCategory I J W κ hW hRight hAcyclic
  let dI := (OriginalGeneratedModelAtCardinal.cofibrantFactorizationData
    I J W κ hW hRight hAcyclic).factorizationData a.hom
  let dJ := (OriginalGeneratedModelAtCardinal.fibrantFactorizationData
    I J W κ hW hRight hAcyclic).factorizationData a.hom
  exact ⟨dI.hi, dI.hp, dI.fac, dJ.hi, dJ.hp, dJ.fac⟩

-- Naturality checks the entire I-middle action on an arbitrary original Arrow map.
example {a b : Arrow C} (φ : a ⟶ b) :
    letI : ModelCategory C :=
      OriginalGeneratedModelAtCardinal.modelCategory I J W κ hW hRight hAcyclic
    let d := OriginalGeneratedModelAtCardinal.cofibrantFactorizationData
      I J W κ hW hRight hAcyclic
    φ.left ≫ d.i.app b = d.i.app a ≫ SmallObject.objMap I κ φ ∧
      SmallObject.objMap I κ φ ≫ d.p.app b = d.p.app a ≫ φ.right := by
  letI : ModelCategory C :=
    OriginalGeneratedModelAtCardinal.modelCategory I J W κ hW hRight hAcyclic
  dsimp only
  let d := OriginalGeneratedModelAtCardinal.cofibrantFactorizationData
    I J W κ hW hRight hAcyclic
  have hi := d.i.naturality φ
  have hp := d.p.naturality φ
  have hMap := OriginalGeneratedModelAtCardinal.cofibrantFactorizationData_map
    I J W κ hW hRight hAcyclic φ
  change d.Z.map φ = SmallObject.objMap I κ φ at hMap
  rw [hMap] at hi hp
  exact ⟨hi, hp⟩

-- Naturality also retains the complete J-middle action, with its distinct original family.
example {a b : Arrow C} (φ : a ⟶ b) :
    letI : ModelCategory C :=
      OriginalGeneratedModelAtCardinal.modelCategory I J W κ hW hRight hAcyclic
    let d := OriginalGeneratedModelAtCardinal.fibrantFactorizationData
      I J W κ hW hRight hAcyclic
    φ.left ≫ d.i.app b = d.i.app a ≫ SmallObject.objMap J κ φ ∧
      SmallObject.objMap J κ φ ≫ d.p.app b = d.p.app a ≫ φ.right := by
  letI : ModelCategory C :=
    OriginalGeneratedModelAtCardinal.modelCategory I J W κ hW hRight hAcyclic
  dsimp only
  let d := OriginalGeneratedModelAtCardinal.fibrantFactorizationData
    I J W κ hW hRight hAcyclic
  have hi := d.i.naturality φ
  have hp := d.p.naturality φ
  have hMap := OriginalGeneratedModelAtCardinal.fibrantFactorizationData_map
    I J W κ hW hRight hAcyclic φ
  change d.Z.map φ = SmallObject.objMap J κ φ at hMap
  rw [hMap] at hi hp
  exact ⟨hi, hp⟩

end FixedCardinalRecognition

section CommonCardinal

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [IsLocallyPresentable.{w} C] (I J : MorphismProperty C)
  [I.HasSmallObjectArgument.{w}] [J.HasSmallObjectArgument.{w}]
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)

-- Synchronize the LP and two SOA witnesses, then build actual generation data with the same banks.
example :
    ∃ (κ : Cardinal.{w}) (hκ : Fact κ.IsRegular) (hb : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hb
      IsCardinalLocallyPresentable C κ ∧
        ∃ d : CofibrantGenerationData C κ, d.I = I ∧ d.J = J ∧
          d.I.rlp = trivialFibrations C ∧ d.J.rlp = fibrations C ∧
          (∀ a : Arrow C,
            let dI := d.cofibrantFactorizationData.factorizationData a.hom
            let dJ := d.fibrantFactorizationData.factorizationData a.hom
            cofibrations C dI.i ∧ trivialFibrations C dI.p ∧ dI.i ≫ dI.p = a.hom ∧
              trivialCofibrations C dJ.i ∧ fibrations C dJ.p ∧ dJ.i ≫ dJ.p = a.hom) := by
  obtain ⟨κ, hκ, hb, hLP, hIκ, hJκ⟩ := exists_common_generation_cardinal I J
  letI : Fact κ.IsRegular := hκ
  letI : OrderBot κ.ord.ToType := hb
  let d : CofibrantGenerationData C κ :=
    { I := I, J := J, I_smallObject := hIκ, J_smallObject := hJκ,
      I_rlp := hI, J_rlp := hJ }
  refine ⟨κ, hκ, hb, hLP, d, rfl, rfl, d.I_rlp, d.J_rlp, ?_⟩
  intro a
  let dI := d.cofibrantFactorizationData.factorizationData a.hom
  let dJ := d.fibrantFactorizationData.factorizationData a.hom
  exact ⟨dI.hi, dI.hp, dI.fac, dJ.hi, dJ.hp, dJ.fac⟩

-- The same supplied right-class equations earn combinatoriality after synchronization.
example : IsCombinatorialModelCategory.{w} C :=
  isCombinatorialModelCategory_of_generators I J hI hJ

end CommonCardinal

end MathlibExtTest.AlgebraicTopology.ModelCategory.GenerationAPI
