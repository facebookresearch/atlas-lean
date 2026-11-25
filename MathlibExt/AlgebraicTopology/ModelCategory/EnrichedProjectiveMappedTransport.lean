/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveMappedFactors
import Mathlib.AlgebraicTopology.ModelCategory.Transport
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.WholeEquivalence

/-!
# Constructing projective models on the exact original source carriers

The genuine target model is produced from the actual base generator and
mapped source-cell data. The complete original carrier equivalence then
constructs all source model classes and transports the same actual factor
objects/maps. No source or target spectral model is an input.
-/

set_option autoImplicit false

noncomputable section

universe w uA uV vV uC vC

open CategoryTheory Limits MorphismProperty Opposite MonoidalCategory

namespace HomotopicalAlgebra.EnrichedProjective.MappedSources

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]
  {C : Type uC} [Category.{vC} C]
  (d : CofibrantGenerationData V κ)
  (hJ : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y), d.J f → trivialCofibrations V (f ▷ (a ⟶[V] b)))
  (hSourceI : SourceCondition (A := A) (κ := κ) d.I)
  (hSourceJ : SourceCondition (A := A) (κ := κ) d.J)

/-- The actual weak class on the original carrier is the inverse of the constructed genuine weak
class. -/
def sourceWeakProperty (e : C ≌ EnrichedFunctorCat V A) : MorphismProperty C :=
  (modelCategory d hJ hSourceI hSourceJ).categoryWithWeakEquivalences.weakEquivalences.inverseImage
      e.functor

/-- The actual cofibration class on the original carrier comes from the constructed literal free I
model. -/
def sourceCofibrationProperty (e : C ≌ EnrichedFunctorCat V A) : MorphismProperty C :=
  (modelCategory d hJ hSourceI hSourceJ).categoryWithCofibrations.cofibrations.inverseImage
      e.functor

/-- The actual fibration class on the original carrier is the inverse of the constructed genuine
fibration class. -/
def sourceFibrationProperty (e : C ≌ EnrichedFunctorCat V A) : MorphismProperty C :=
  (modelCategory d hJ hSourceI hSourceJ).categoryWithFibrations.fibrations.inverseImage e.functor

/-- The model is constructed on the same original source carrier from the actual produced target
model. -/
@[instance_reducible]
def sourceModelCategory (e : C ≌ EnrichedFunctorCat V A) : ModelCategory C := by
  letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  letI : CategoryWithCofibrations C := ⟨sourceCofibrationProperty d hJ hSourceI hSourceJ e⟩
  letI : CategoryWithFibrations C := ⟨sourceFibrationProperty d hJ hSourceI hSourceJ e⟩
  letI : CategoryWithWeakEquivalences C := ⟨sourceWeakProperty d hJ hSourceI hSourceJ e⟩
  exact ModelCategory.transport e rfl rfl rfl

include hJ hSourceI hSourceJ

/-- The entire original source weak class is retained through the actual carrier functor. -/
theorem sourceModelCategory_weak (e : C ≌ EnrichedFunctorCat V A) :
    (sourceModelCategory d hJ hSourceI hSourceJ e).categoryWithWeakEquivalences.weakEquivalences =
      sourceWeakProperty d hJ hSourceI hSourceJ e := rfl

/-- The entire original source cofibration class is retained through the actual carrier functor. -/
theorem sourceModelCategory_cof (e : C ≌ EnrichedFunctorCat V A) :
    (sourceModelCategory d hJ hSourceI hSourceJ e).categoryWithCofibrations.cofibrations =
      sourceCofibrationProperty d hJ hSourceI hSourceJ e := rfl

/-- The entire original source fibration class is retained through the actual carrier functor. -/
theorem sourceModelCategory_fib (e : C ≌ EnrichedFunctorCat V A) :
    (sourceModelCategory d hJ hSourceI hSourceJ e).categoryWithFibrations.fibrations =
      sourceFibrationProperty d hJ hSourceI hSourceJ e := rfl

/-- The exact original source trivial-fibration class is the complete mapped target intersection. -/
theorem sourceModelCategory_trivialFib (e : C ≌ EnrichedFunctorCat V A) :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    letI : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
    trivialFibrations C = (trivialFibrations (EnrichedFunctorCat V A)).inverseImage e.functor := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  let _ : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
  rfl

/-- The exact original source trivial-cofibration class is the complete mapped target intersection.
-/
theorem sourceModelCategory_trivialCof (e : C ≌ EnrichedFunctorCat V A) :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    letI : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
    trivialCofibrations C = (trivialCofibrations (EnrichedFunctorCat V A)).inverseImage e.functor
        := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  let _ : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
  rfl

/-- The actual same-cardinal I factor value is retained with the original carrier inverse and all
maps. -/
def sourceCofibrantFactorizationData (e : C ≌ EnrichedFunctorCat V A) :
    letI : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  let _ : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
  exact (cofibrantFactorizationData d hJ hSourceI hSourceJ).ofEquivalence e

/-- The actual same-cardinal J factor value is retained with the original carrier inverse and all
maps. -/
def sourceFibrantFactorizationData (e : C ≌ EnrichedFunctorCat V A) :
    letI : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
    FunctorialFactorizationData (trivialCofibrations C) (fibrations C) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  let _ : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
  exact (fibrantFactorizationData d hJ hSourceI hSourceJ).ofEquivalence e

/-- Every original I factor pair composes to the entire caller source arrow. -/
theorem sourceCofibrantFactorizationData_fac (e : C ≌ EnrichedFunctorCat V A) (f : Arrow C) :
    letI : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
    let data := sourceCofibrantFactorizationData d hJ hSourceI hSourceJ e
    data.i.app f ≫ data.p.app f = f.hom :=
  (sourceCofibrantFactorizationData d hJ hSourceI hSourceJ e).fac_app

/-- Every original J factor pair composes to the entire caller source arrow. -/
theorem sourceFibrantFactorizationData_fac (e : C ≌ EnrichedFunctorCat V A) (f : Arrow C) :
    letI : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
    let data := sourceFibrantFactorizationData d hJ hSourceI hSourceJ e
    data.i.app f ≫ data.p.app f = f.hom :=
  (sourceFibrantFactorizationData d hJ hSourceI hSourceJ e).fac_app

end HomotopicalAlgebra.EnrichedProjective.MappedSources
