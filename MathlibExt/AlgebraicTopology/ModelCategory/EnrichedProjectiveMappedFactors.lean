/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveMappedSources
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization

/-!
# Original same-cardinal factors for the mapped-source projective model

The actual free I/J families, caller ordinal bottom and κ iteration remain
unchanged. All intermediate functor and natural-map fields are the original
small-object data; only membership in the constructed model classes is transported.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uA uV vV

open CategoryTheory Limits MorphismProperty Opposite MonoidalCategory

namespace HomotopicalAlgebra.EnrichedProjective.MappedSources

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]
  (d : CofibrantGenerationData V κ)
  (hJ : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y), d.J f → trivialCofibrations V (f ▷ (a ⟶[V] b)))
  (hSourceI : SourceCondition (A := A) (κ := κ) d.I)
  (hSourceJ : SourceCondition (A := A) (κ := κ) d.J)

include hJ hSourceI hSourceJ

/-- The actual free I family has the returned model's entire trivial-fibration class. -/
theorem generatorsI_rlp :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    (generators (A := A) d.I).rlp = trivialFibrations (EnrichedFunctorCat V A) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  rw [trivialFibrations_eq d hJ hSourceI hSourceJ]
  rw [EvaluationTransfer.evaluatedGenerators_rlp_eq
    (fun a : A => EnrichedFunctorCat.Free.functor a)
    (fun a : A => EnrichedFunctorCat.evaluation a)
    (fun a => EnrichedFunctorCat.Free.adjunction a) d.I, d.I_rlp]

/-- The actual free J family has the returned model's entire fibration class. -/
theorem generatorsJ_rlp :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    (generators (A := A) d.J).rlp = fibrations (EnrichedFunctorCat V A) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  rw [fibrations_eq d hJ hSourceI hSourceJ]
  rw [EvaluationTransfer.evaluatedGenerators_rlp_eq
    (fun a : A => EnrichedFunctorCat.Free.functor a)
    (fun a : A => EnrichedFunctorCat.evaluation a)
    (fun a => EnrichedFunctorCat.Free.adjunction a) d.J, d.J_rlp]

/-- Actual generation on the same model, original free families, κ and caller bottom. -/
def generationData :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    CofibrantGenerationData (EnrichedFunctorCat V A) κ := by
  letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  exact
    { I := generators (A := A) d.I
      J := generators (A := A) d.J
      I_smallObject := generators_isCardinal d.I hSourceI
      J_smallObject := generators_isCardinal d.J hSourceJ
      I_rlp := generatorsI_rlp d hJ hSourceI hSourceJ
      J_rlp := generatorsJ_rlp d hJ hSourceI hSourceJ }

/-- The entire original free I generator family is retained. -/
theorem generationData_I :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    (generationData d hJ hSourceI hSourceJ).I = generators (A := A) d.I := rfl

/-- The entire original free J generator family is retained. -/
theorem generationData_J :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    (generationData d hJ hSourceI hSourceJ).J = generators (A := A) d.J := rfl

/-- The actual same-κ I iteration gives the original cofibration/trivial-fibration factor data. -/
def cofibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    FunctorialFactorizationData (cofibrations (EnrichedFunctorCat V A))
      (trivialFibrations (EnrichedFunctorCat V A)) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  let _ : (generators (A := A) d.I).IsCardinalForSmallObjectArgument κ := generators_isCardinal d.I
      hSourceI
  exact (SmallObject.functorialFactorizationData (generators (A := A) d.I) κ).ofLE
    (cofibrations_eq d hJ hSourceI hSourceJ).symm.le (generatorsI_rlp d hJ hSourceI hSourceJ).le

/-- The actual same-κ J iteration gives the original trivial-cofibration/fibration factor data. -/
def fibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    FunctorialFactorizationData (trivialCofibrations (EnrichedFunctorCat V A))
      (fibrations (EnrichedFunctorCat V A)) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  let _ : (generators (A := A) d.J).IsCardinalForSmallObjectArgument κ := generators_isCardinal d.J
      hSourceJ
  exact (SmallObject.functorialFactorizationData (generators (A := A) d.J) κ).ofLE
    (trivialCofibrations_eq d hJ hSourceI hSourceJ).symm.le
        (generatorsJ_rlp d hJ hSourceI hSourceJ).le

/-- The complete I middle functor and both natural maps are precisely the original κ data. -/
theorem cofibrantFactorizationData_fields :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    letI : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    letI : (generators (A := A) d.I).IsCardinalForSmallObjectArgument κ := generators_isCardinal
        d.I hSourceI
    let data := cofibrantFactorizationData d hJ hSourceI hSourceJ
    let original := SmallObject.functorialFactorizationData (generators (A := A) d.I) κ
    data.Z = original.Z ∧ data.i = original.i ∧ data.p = original.p := ⟨rfl, rfl, rfl⟩

/-- The complete J middle functor and both natural maps are precisely the original κ data. -/
theorem fibrantFactorizationData_fields :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    letI : d.J.IsSmall.{w} := d.J_smallObject.isSmall
    letI : (generators (A := A) d.J).IsCardinalForSmallObjectArgument κ := generators_isCardinal
        d.J hSourceJ
    let data := fibrantFactorizationData d hJ hSourceI hSourceJ
    let original := SmallObject.functorialFactorizationData (generators (A := A) d.J) κ
    data.Z = original.Z ∧ data.i = original.i ∧ data.p = original.p := ⟨rfl, rfl, rfl⟩

/-- The complete I factor maps compose to the original caller arrow. -/
theorem cofibrantFactorizationData_fac (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    let data := cofibrantFactorizationData d hJ hSourceI hSourceJ
    data.i.app f ≫ data.p.app f = f.hom :=
        (cofibrantFactorizationData d hJ hSourceI hSourceJ).fac_app

/-- The complete J factor maps compose to the original caller arrow. -/
theorem fibrantFactorizationData_fac (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    let data := fibrantFactorizationData d hJ hSourceI hSourceJ
    data.i.app f ≫ data.p.app f = f.hom := (fibrantFactorizationData d hJ hSourceI hSourceJ).fac_app

end HomotopicalAlgebra.EnrichedProjective.MappedSources
