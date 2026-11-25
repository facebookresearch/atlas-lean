/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveGeneratorCells

set_option autoImplicit false
noncomputable section
universe w uA uV vV

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Opposite
open MonoidalCategory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective

namespace MathlibExtTest.EnrichedProjectiveGeneratorCells

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]
  (d : CofibrantGenerationData V κ) (QI QJ : MorphismProperty V)
  [QI.RespectsIso] [QJ.RespectsIso]
  [QI.IsStableUnderCoproducts.{w}] [QJ.IsStableUnderCoproducts.{w}]
  [QI.IsStableUnderCobaseChange] [QJ.IsStableUnderCobaseChange]
  [QI.IsStableUnderTransfiniteComposition.{w}]
  [QJ.IsStableUnderTransfiniteComposition.{w}]
  (hI : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
    d.I f → QI (f ▷ (a ⟶[V] b)))
  (hJ : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
    d.J f → QJ (f ▷ (a ⟶[V] b)))
  (hSourceI : ∀ {X Y : V} (f : X ⟶ Y), d.I f →
    ∀ (F : κ.ord.ToType ⥤ V) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), QI (F.map φ)) →
      PreservesColimit F (coyoneda.obj (op X)))
  (hSourceJ : ∀ {X Y : V} (f : X ⟶ Y), d.J f →
    ∀ (F : κ.ord.ToType ⥤ V) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), QJ (F.map φ)) →
      PreservesColimit F (coyoneda.obj (op X)))
  (hCells : ∀ (b : A) {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y),
    RelativeCellComplex.{w}
      (fun (_ : κ.ord.ToType) => (generators (A := A) d.J).homFamily) f →
    weakEquivalences V ((EnrichedFunctorCat.evaluation b).map f))

-- No target model, target SOA, whole-left bound, monoid axiom or Hom-cofibrancy input.
example : ModelCategory (EnrichedFunctorCat V A) :=
  modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    weakEquivalences (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences V) :=
  GeneratorCells.weakEquivalences_eq d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    cofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.I).rlp.llp :=
  GeneratorCells.cofibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    fibrations (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations V) :=
  GeneratorCells.fibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    trivialFibrations (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations V) :=
  GeneratorCells.trivialFibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    trivialCofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.J).rlp.llp :=
  GeneratorCells.trivialCofibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells

example (a : A) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (EnrichedFunctorCat.Free.adjunction (V := V) a).IsQuillenAdjunction :=
  GeneratorCells.freeAtEvaluation_isQuillenAdjunction d QI QJ hI hJ hSourceI hSourceJ hCells a

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    HasFunctorialFactorization (cofibrations (EnrichedFunctorCat V A))
        (trivialFibrations (EnrichedFunctorCat V A)) ∧
      HasFunctorialFactorization (trivialCofibrations (EnrichedFunctorCat V A))
        (fibrations (EnrichedFunctorCat V A)) :=
  GeneratorCells.functorialFactorizations d QI QJ hI hJ hSourceI hSourceJ hCells

-- Exact same-cardinal I data: object, every map, both natural arrows and original equation.
example (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    letI : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    letI : (generators (A := A) d.I).IsCardinalForSmallObjectArgument κ :=
      generators_isCardinalForSmallObjectArgument d.I QI hI hSourceI
    let data := GeneratorCells.cofibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
    data.Z.obj f = SmallObject.obj (generators (A := A) d.I) κ f.hom := by
  rfl

example {f g : Arrow (EnrichedFunctorCat V A)} (φ : f ⟶ g) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    letI : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    letI : (generators (A := A) d.I).IsCardinalForSmallObjectArgument κ :=
      generators_isCardinalForSmallObjectArgument d.I QI hI hSourceI
    let data := GeneratorCells.cofibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
    data.Z.map φ = SmallObject.objMap (generators (A := A) d.I) κ φ := by
  rfl

example (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    letI : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    letI : (generators (A := A) d.I).IsCardinalForSmallObjectArgument κ :=
      generators_isCardinalForSmallObjectArgument d.I QI hI hSourceI
    let data := GeneratorCells.cofibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
    data.i.app f = SmallObject.ιObj (generators (A := A) d.I) κ f.hom ∧
      data.p.app f = SmallObject.πObj (generators (A := A) d.I) κ f.hom := by
  exact ⟨rfl, rfl⟩

example (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := GeneratorCells.cofibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
    cofibrations (EnrichedFunctorCat V A) (data.i.app f) ∧
      trivialFibrations (EnrichedFunctorCat V A) (data.p.app f) ∧
      data.i.app f ≫ data.p.app f = f.hom := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  let data := GeneratorCells.cofibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
  exact ⟨data.hi f, data.hp f, GeneratorCells.cofibrantFactorizationData_fac
    d QI QJ hI hJ hSourceI hSourceJ hCells f⟩

-- Exact same-cardinal J data, with the same four structural comparisons.
example (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    letI : d.J.IsSmall.{w} := d.J_smallObject.isSmall
    letI : (generators (A := A) d.J).IsCardinalForSmallObjectArgument κ :=
      generators_isCardinalForSmallObjectArgument d.J QJ hJ hSourceJ
    let data := GeneratorCells.fibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
    data.Z.obj f = SmallObject.obj (generators (A := A) d.J) κ f.hom := by
  rfl

example {f g : Arrow (EnrichedFunctorCat V A)} (φ : f ⟶ g) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    letI : d.J.IsSmall.{w} := d.J_smallObject.isSmall
    letI : (generators (A := A) d.J).IsCardinalForSmallObjectArgument κ :=
      generators_isCardinalForSmallObjectArgument d.J QJ hJ hSourceJ
    let data := GeneratorCells.fibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
    data.Z.map φ = SmallObject.objMap (generators (A := A) d.J) κ φ := by
  rfl

example (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    letI : d.J.IsSmall.{w} := d.J_smallObject.isSmall
    letI : (generators (A := A) d.J).IsCardinalForSmallObjectArgument κ :=
      generators_isCardinalForSmallObjectArgument d.J QJ hJ hSourceJ
    let data := GeneratorCells.fibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
    data.i.app f = SmallObject.ιObj (generators (A := A) d.J) κ f.hom ∧
      data.p.app f = SmallObject.πObj (generators (A := A) d.J) κ f.hom := by
  exact ⟨rfl, rfl⟩

example (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := GeneratorCells.fibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
    trivialCofibrations (EnrichedFunctorCat V A) (data.i.app f) ∧
      fibrations (EnrichedFunctorCat V A) (data.p.app f) ∧
      data.i.app f ≫ data.p.app f = f.hom := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  let data := GeneratorCells.fibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
  exact ⟨data.hi f, data.hp f, GeneratorCells.fibrantFactorizationData_fac
    d QI QJ hI hJ hSourceI hSourceJ hCells f⟩

#check @modelCategoryOfGeneratorCells
#check @GeneratorCells.weakEquivalences_eq
#check @GeneratorCells.cofibrations_eq
#check @GeneratorCells.fibrations_eq
#check @GeneratorCells.trivialFibrations_eq
#check @GeneratorCells.trivialCofibrations_eq
#check @GeneratorCells.cofibrantFactorizationData
#check @GeneratorCells.fibrantFactorizationData
#check @GeneratorCells.cofibrantFactorizationData_fields
#check @GeneratorCells.fibrantFactorizationData_fields
#check @GeneratorCells.cofibrantFactorizationData_fac
#check @GeneratorCells.fibrantFactorizationData_fac
#check @GeneratorCells.functorialFactorizations
#check @GeneratorCells.freeAtEvaluation_isQuillenAdjunction

#print axioms modelCategoryOfGeneratorCells
#print axioms GeneratorCells.weakEquivalences_eq
#print axioms GeneratorCells.cofibrations_eq
#print axioms GeneratorCells.fibrations_eq
#print axioms GeneratorCells.trivialFibrations_eq
#print axioms GeneratorCells.trivialCofibrations_eq
#print axioms GeneratorCells.cofibrantFactorizationData
#print axioms GeneratorCells.fibrantFactorizationData
#print axioms GeneratorCells.cofibrantFactorizationData_fields
#print axioms GeneratorCells.fibrantFactorizationData_fields
#print axioms GeneratorCells.cofibrantFactorizationData_fac
#print axioms GeneratorCells.fibrantFactorizationData_fac
#print axioms GeneratorCells.functorialFactorizations
#print axioms GeneratorCells.freeAtEvaluation_isQuillenAdjunction

end MathlibExtTest.EnrichedProjectiveGeneratorCells
