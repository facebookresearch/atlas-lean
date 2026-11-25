/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveGeneratorCells
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
public import MathlibExt.CategoryTheory.MorphismProperty.Factorization.GivenDataEquality

/-!
# Generation data for the original enriched generator-cell model

The actual original enriched factory, free generator families, cardinal and
all source/cardinal-cell hypotheses remain unchanged. The returned generation
record exposes their existing complete eligibility and class proofs. Generic
fixed-generation factor getters retain the original Z/i/p data and their laws.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w uA uV vV
open CategoryTheory Limits MorphismProperty Opposite MonoidalCategory

namespace HomotopicalAlgebra.EnrichedProjective.GeneratorCells

section OriginalModelData

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
  (hI : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y), d.I f → QI (f ▷ (a ⟶[V] b)))
  (hJ : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y), d.J f → QJ (f ▷ (a ⟶[V] b)))
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
      (fun _ : κ.ord.ToType => (generators (A := A) d.J).homFamily) f →
      weakEquivalences V ((EnrichedFunctorCat.evaluation b).map f))

include hI hJ hSourceI hSourceJ hCells

/-- The original I free family has the selected model's complete trivial-fibration class. -/
theorem generatorsI_rlp_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (generators (A := A) d.I).rlp = trivialFibrations (EnrichedFunctorCat V A) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  rw [trivialFibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells]
  rw [EvaluationTransfer.evaluatedGenerators_rlp_eq
    (fun a : A => EnrichedFunctorCat.Free.functor a)
    (fun a : A => EnrichedFunctorCat.evaluation a)
    (fun a => EnrichedFunctorCat.Free.adjunction a) d.I, d.I_rlp]

/-- The original J free family has the selected model's complete fibration class. -/
theorem generatorsJ_rlp_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (generators (A := A) d.J).rlp = fibrations (EnrichedFunctorCat V A) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  rw [fibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells]
  rw [EvaluationTransfer.evaluatedGenerators_rlp_eq
    (fun a : A => EnrichedFunctorCat.Free.functor a)
    (fun a : A => EnrichedFunctorCat.evaluation a)
    (fun a => EnrichedFunctorCat.Free.adjunction a) d.J, d.J_rlp]

/-- Return actual generation data on the same original enriched model at the supplied κ. -/
def generationData :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    CofibrantGenerationData (EnrichedFunctorCat V A) κ := by
  letI : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  exact
    { I := generators (A := A) d.I
      J := generators (A := A) d.J
      I_smallObject := generators_isCardinalForSmallObjectArgument d.I QI hI hSourceI
      J_smallObject := generators_isCardinalForSmallObjectArgument d.J QJ hJ hSourceJ
      I_rlp := generatorsI_rlp_eq d QI QJ hI hJ hSourceI hSourceJ hCells
      J_rlp := generatorsJ_rlp_eq d QI QJ hI hJ hSourceI hSourceJ hCells }

/-- The entire original enriched I family is retained, including every source label. -/
theorem generationData_I :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (generationData d QI QJ hI hJ hSourceI hSourceJ hCells).I = generators (A := A) d.I := rfl

/-- The entire original enriched J family is retained, including every source label. -/
theorem generationData_J :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (generationData d QI QJ hI hJ hSourceI hSourceJ hCells).J = generators (A := A) d.J := rfl

/-- The complete actual I eligibility dictionary is the original factory source proof. -/
theorem generationData_I_smallObject :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    letI : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    (generationData d QI QJ hI hJ hSourceI hSourceJ hCells).I_smallObject =
      generators_isCardinalForSmallObjectArgument d.I QI hI hSourceI := rfl

/-- The complete actual J eligibility dictionary is the original factory source proof. -/
theorem generationData_J_smallObject :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    letI : d.J.IsSmall.{w} := d.J_smallObject.isSmall
    (generationData d QI QJ hI hJ hSourceI hSourceJ hCells).J_smallObject =
      generators_isCardinalForSmallObjectArgument d.J QJ hJ hSourceJ := rfl

/-- The generation record's complete I left class is the original enriched cofibration class. -/
theorem generationData_I_left :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (generationData d QI QJ hI hJ hSourceI hSourceJ hCells).I.rlp.llp =
      cofibrations (EnrichedFunctorCat V A) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  rw [generationData_I, ← cofibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells]

/-- The generation record's complete J left class is the original trivial-cofibration class. -/
theorem generationData_J_left :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (generationData d QI QJ hI hJ hSourceI hSourceJ hCells).J.rlp.llp =
      trivialCofibrations (EnrichedFunctorCat V A) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  rw [generationData_J, ← trivialCofibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells]

/-- All five model classes belong to the same actual original enriched factory. -/
theorem generationData_five_classes :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    weakEquivalences (EnrichedFunctorCat V A) =
        EvaluationTransfer.evaluationProperty
          (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences V) ∧
      fibrations (EnrichedFunctorCat V A) =
        EvaluationTransfer.evaluationProperty
          (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations V) ∧
      trivialFibrations (EnrichedFunctorCat V A) =
        EvaluationTransfer.evaluationProperty
          (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations V) ∧
      cofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.I).rlp.llp ∧
      trivialCofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.J).rlp.llp :=
  ⟨weakEquivalences_eq d QI QJ hI hJ hSourceI hSourceJ hCells,
    fibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells,
    trivialFibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells,
    cofibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells,
    trivialCofibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells⟩

/-- The generic fixed I getter returns the exact entire original enriched factor value. -/
theorem generationData_cofibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (CofibrantGenerationData.cofibrantFactorizationData
        (generationData d QI QJ hI hJ
          hSourceI hSourceJ hCells)) =
      cofibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  apply FunctorialFactorizationData.eq_of_middle_and_heq_natural_maps
  · rfl
  · rfl
  · rfl

/-- The generic fixed J getter returns the exact entire original enriched factor value. -/
theorem generationData_fibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (CofibrantGenerationData.fibrantFactorizationData
        (generationData d QI QJ hI hJ
          hSourceI hSourceJ hCells)) =
      fibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  apply FunctorialFactorizationData.eq_of_middle_and_heq_natural_maps
  · rfl
  · rfl
  · rfl

end OriginalModelData

section OriginalCoefficientFunctions

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {A : Type uA} [EnrichedCategory V A]

/-- The actual chosen unit uses original identity evaluation at each free object. -/
theorem original_free_unit_function (a : A) :
    (EnrichedFunctorCat.Free.adjunction (V := V) a).unit.app =
      (fun X => EnrichedFunctorCat.Free.evaluate a X
        ((EnrichedFunctorCat.Free.functor (V := V) (A := A) a).obj X) (𝟙 _)) := by
  funext X
  rw [← Adjunction.homEquiv_id]
  rw [EnrichedFunctorCat.Free.adjunction_homEquiv]
  rfl

/-- The actual chosen counit is the original extension of the identity coefficient. -/
theorem original_free_counit_function (a : A) :
    (EnrichedFunctorCat.Free.adjunction (V := V) a).counit.app =
      (fun F : EnrichedFunctorCat V A => EnrichedFunctorCat.Free.extend (V := V) (A := A) a
        ((EnrichedFunctorCat.evaluation (V := V) (A := A) a).obj F) F
        (𝟙 ((EnrichedFunctorCat.evaluation (V := V) (A := A) a).obj F))) := by
  funext F
  rw [← Adjunction.homEquiv_symm_id]
  rw [EnrichedFunctorCat.Free.adjunction_homEquiv]
  rfl

end OriginalCoefficientFunctions

end HomotopicalAlgebra.EnrichedProjective.GeneratorCells
