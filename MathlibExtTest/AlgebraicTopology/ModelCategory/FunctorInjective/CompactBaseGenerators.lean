/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.CompactBaseGenerators

/-!
# Entire compact scalar enlargement and original base generation contracts

The original I remains the actual public base generation data. Auxiliary
compact representatives retain original endpoints, whole Arrow isomorphisms
and complete native fixed-rank factors. Saturation is proved on the actual
base category; no compactness of an arbitrary tree root is asserted.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits
open HomotopicalAlgebra HomotopicalAlgebra.FunctorInjective
open CategoryTheory.MorphismProperty

namespace MathlibExtTest.FunctorInjectiveCompactBaseGenerators

section OriginalScalarFamily

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {χ : Cardinal.{w}} [Fact χ.IsRegular] (b : CompactBaseGeneratorData C χ)

/-- The auxiliary generating family is genuinely working-small. -/
theorem actual_auxiliary_family_small : b.generators.IsSmall.{w} := inferInstance

/-- Every auxiliary generator keeps its actual original scalar Arrow and both endpoints. -/
theorem actual_auxiliary_arrow_properties (k : b.index) :
    cofibrations C (b.arrow k).hom ∧
      IsCardinalPresentable (b.arrow k).left χ ∧
      IsCardinalPresentable (b.arrow k).right χ := b.arrow_properties k

/-- The entire auxiliary family is contained in the original base cofibration class. -/
theorem actual_auxiliary_family_membership : b.generators ≤ cofibrations C :=
  b.generators_le_cofibrations

/-- The owner retains a whole original representative isomorphism. -/
def actualRepresentative (p : Arrow C) (hp : compactBaseCofibrationArrows C χ p) :
    Σ k : b.index, p ≅ b.arrow k :=
  ⟨b.representative p hp, b.representativeIso p hp⟩

/-- Both original scalar endpoints retain the forward original square equation. -/
theorem actualRepresentative_square (p : Arrow C)
    (hp : compactBaseCofibrationArrows C χ p) :
    (actualRepresentative b p hp).2.hom.left ≫
        (b.arrow (actualRepresentative b p hp).1).hom =
      p.hom ≫ (actualRepresentative b p hp).2.hom.right :=
  b.representative_square p hp

/-- Both original scalar endpoints retain the inverse original square equation. -/
theorem actualRepresentative_inverse_square (p : Arrow C)
    (hp : compactBaseCofibrationArrows C χ p) :
    (actualRepresentative b p hp).2.inv.left ≫ p.hom =
      (b.arrow (actualRepresentative b p hp).1).hom ≫
        (actualRepresentative b p hp).2.inv.right :=
  b.representative_inverse_square p hp

/-- An incoming original scalar square is recovered after its actual representative conjugation. -/
theorem originalSquare_recovery {p q : Arrow C}
    (hp : compactBaseCofibrationArrows C χ p) (f : p ⟶ q) :
    (b.representativeIso p hp).hom ≫ ((b.representativeIso p hp).inv ≫ f) = f := by
  simp

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  (hSource : ∀ i : d.I.toSet, IsCardinalPresentable i.1.left χ)
  (hTarget : ∀ i : d.I.toSet, IsCardinalPresentable i.1.right χ)

/-- Every actual original I generator is an original base cofibration. -/
theorem originalI_actual_cofibration (i : d.I.toSet) : cofibrations C i.1.hom :=
  CompactBaseGeneratorData.originalI_cofibration d i

include hSource hTarget in
/-- Both endpoints of every original I generator have the justified compact bound. -/
theorem originalI_actual_compact (i : d.I.toSet) :
    compactBaseCofibrationArrows C χ i.1 :=
  CompactBaseGeneratorData.originalI_compact d hSource hTarget i

/-- The complete original I comparison is an actual scalar Arrow isomorphism. -/
def originalIWholeComparison (i : d.I.toSet) :
    i.1 ≅ b.arrow (b.originalIRepresentative d hSource hTarget i) :=
  b.originalIRepresentativeIso d hSource hTarget i

/-- Both original I endpoint maps commute with the actual original I Arrow. -/
theorem originalIWholeComparison_square (i : d.I.toSet) :
    (originalIWholeComparison b d hSource hTarget i).hom.left ≫
        (b.arrow (b.originalIRepresentative d hSource hTarget i)).hom =
      i.1.hom ≫ (originalIWholeComparison b d hSource hTarget i).hom.right :=
  (originalIWholeComparison b d hSource hTarget i).hom.w

include hSource hTarget in
/-- All original I generator values belong to the actual auxiliary iso closure. -/
theorem originalI_covered : d.I ≤ b.generators.isoClosure :=
  b.originalI_le_isoClosure d hSource hTarget

include d hSource hTarget in
/-- Both complete original scalar lifting classes are inspected. -/
theorem all_original_base_lifting_classes :
    b.generators.rlp = trivialFibrations C ∧
      b.generators.rlp.llp = cofibrations C :=
  ⟨b.generators_rlp_eq d hSource hTarget, b.generators_rlp_llp_eq d hSource hTarget⟩

variable [IsCardinalLocallyPresentable C χ]

/-- All six original scalar eligibility fields are returned at the actual compact rank. -/
theorem all_scalar_eligibility :
    let _ : OrderBot χ.ord.ToType := boundedOrdinalBottom χ
    b.generators.IsCardinalForSmallObjectArgument χ := by
  let _ : OrderBot χ.ord.ToType := boundedOrdinalBottom χ
  exact b.eligible

include d hSource hTarget in
/-- The actual weak saturation is the entire original base cofibration class. -/
theorem actual_original_scalar_saturation :
    (MorphismProperty.transfiniteCompositions.{w}
      (MorphismProperty.coproducts.{w} b.generators).pushouts).retracts = cofibrations C :=
  b.cellular_saturation_eq d hSource hTarget

/-- The owner keeps the actual scalar native factor record whole. -/
def actualNativeFactor : FunctorialFactorizationData b.generators.rlp.llp b.generators.rlp :=
  b.factorization

/-- The entire native factor is the actual selected family's record. -/
theorem actualNativeFactor_eq : actualNativeFactor b = b.factorization := rfl

/-- The native scalar factor retains its complete original strict equation. -/
theorem actualNativeFactor_fac (p : Arrow C) :
    (actualNativeFactor b).i.app p ≫ (actualNativeFactor b).p.app p = p.hom :=
  b.factorization_fac p

/-- The same native middle map occurs in both original scalar Arrow naturality equations. -/
theorem actualNativeFactor_square {p q : Arrow C} (f : p ⟶ q) :
    f.left ≫ (actualNativeFactor b).i.app q =
        (actualNativeFactor b).i.app p ≫ (actualNativeFactor b).Z.map f ∧
      (actualNativeFactor b).Z.map f ≫ (actualNativeFactor b).p.app q =
        (actualNativeFactor b).p.app p ≫ f.right :=
  ⟨(actualNativeFactor b).i.naturality f, (actualNativeFactor b).p.naturality f⟩

end OriginalScalarFamily

section SameActualBoundedProfile

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] {S : Type w} [SmallCategory S] (s : D ≌ S)
  (b : BoundedConstruction d κLP s)

/-- The selected compact scalar family belongs to the same actual original bounded profile. -/
def sameProfileActualBaseFamily : CompactBaseGeneratorData C b.cardinal :=
  sameProfileBaseGenerators d κLP s b

/-- The whole profile-selected base family retains the actual original I Arrow comparisons. -/
def sameProfileOriginalIComparison (i : d.I.toSet) :
    i.1 ≅ (sameProfileActualBaseFamily d κLP s b).arrow
      ((sameProfileActualBaseFamily d κLP s b).originalIRepresentative d
        b.profile.sourceI b.profile.targetI i) :=
  sameProfileOriginalIRepresentativeIso d κLP s b i

/-- The auxiliary scalar family has the entire original base right and left classes. -/
theorem sameProfileActualBaseClasses :
    (sameProfileActualBaseFamily d κLP s b).generators.rlp = trivialFibrations C ∧
      (sameProfileActualBaseFamily d κLP s b).generators.rlp.llp = cofibrations C :=
  ⟨sameProfileBaseGenerators_rlp d κLP s b, sameProfileBaseGenerators_rlp_llp d κLP s b⟩

end SameActualBoundedProfile

end MathlibExtTest.FunctorInjectiveCompactBaseGenerators
