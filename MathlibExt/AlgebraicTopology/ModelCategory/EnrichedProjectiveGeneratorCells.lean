/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective

/-!
# Enriched projective models from actual generator-cardinal cells

Both target small-object arguments and complete evaluated left acyclicity
are derived at the original cardinal. The explicit factorization functors
retain the original intermediate objects, maps and natural arrows.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w uA uV vV

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Opposite
open MonoidalCategory

namespace HomotopicalAlgebra.EnrichedProjective

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]

/-- Construct the genuine enriched projective model from auxiliary source classes
and actual evaluated J-cardinal-cell acyclicity, without the full monoid axiom. -/
@[instance_reducible]
def modelCategoryOfGeneratorCells
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
      weakEquivalences V ((EnrichedFunctorCat.evaluation b).map f)) :
    ModelCategory (EnrichedFunctorCat V A) := by
  let L : A → V ⥤ EnrichedFunctorCat V A :=
    fun a => EnrichedFunctorCat.Free.functor a
  let R : A → EnrichedFunctorCat V A ⥤ V :=
    fun a => EnrichedFunctorCat.evaluation a
  let adj : ∀ a, L a ⊣ R a := fun a => EnrichedFunctorCat.Free.adjunction a
  let _ : HasFiniteLimits (EnrichedFunctorCat V A) := inferInstance
  let _ : HasFiniteColimits (EnrichedFunctorCat V A) := inferInstance
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  let _ : (generators (A := A) d.I).IsCardinalForSmallObjectArgument κ :=
    generators_isCardinalForSmallObjectArgument d.I QI hI hSourceI
  let _ : (generators (A := A) d.J).IsCardinalForSmallObjectArgument κ :=
    generators_isCardinalForSmallObjectArgument d.J QJ hJ hSourceJ
  let _ : (generators (A := A) d.I).HasSmallObjectArgument.{w} :=
    ⟨⟨κ, inferInstance, inferInstance, inferInstance⟩⟩
  let _ : (generators (A := A) d.J).HasSmallObjectArgument.{w} :=
    ⟨⟨κ, inferInstance, inferInstance, inferInstance⟩⟩
  have hBase : d.I.rlp = d.J.rlp ⊓ weakEquivalences V := by
    rw [d.I_rlp, d.J_rlp]
    rfl
  have hAcyclicity : (generators (A := A) d.J).rlp.llp ≤
      EvaluationTransfer.evaluationProperty R (weakEquivalences V) := by
    intro X Y f hf
    apply (EvaluationTransfer.evaluationProperty_iff R (weakEquivalences V) f).2
    intro b
    exact (rlp_llp_le_inverseImage_of_cardinal_cells
      (generators (A := A) d.J) (weakEquivalences V) (R b) κ (hCells b)) f hf
  exact EvaluationTransfer.evaluationProjectiveModelCategory.{w}
    L R adj d.I d.J (weakEquivalences V) hBase hAcyclicity

namespace GeneratorCells

variable (d : CofibrantGenerationData V κ) (QI QJ : MorphismProperty V)
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

include hI hJ hSourceI hSourceJ hCells

/-- Weak equivalences of the selected dictionary are the original evaluated class. -/
theorem weakEquivalences_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    weakEquivalences (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences V) := by
  rfl

/-- Cofibrations retain the original literal free I-generated left class. -/
theorem cofibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    cofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.I).rlp.llp := by
  rfl

/-- Fibrations of the selected dictionary are the original base fibrations at each object. -/
theorem fibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    fibrations (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations V) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  change (generators (A := A) d.J).rlp = _
  rw [EvaluationTransfer.evaluatedGenerators_rlp_eq
    (fun a : A => EnrichedFunctorCat.Free.functor a)
    (fun a : A => EnrichedFunctorCat.evaluation a)
    (fun a => EnrichedFunctorCat.Free.adjunction a) d.J, d.J_rlp]

/-- Trivial fibrations retain the original pointwise base intersection. -/
theorem trivialFibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    trivialFibrations (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations V) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  change fibrations (EnrichedFunctorCat V A) ⊓ weakEquivalences (EnrichedFunctorCat V A) = _
  rw [fibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells,
    weakEquivalences_eq d QI QJ hI hJ hSourceI hSourceJ hCells]
  exact (EvaluationTransfer.evaluationProperty_inf _ (fibrations V) (weakEquivalences V)).symm

/-- Trivial cofibrations retain the complete literal free J-generated left class. -/
theorem trivialCofibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    trivialCofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.J).rlp.llp := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  rw [← fibrations_llp (EnrichedFunctorCat V A)]
  rfl

/-- The explicit I-factorization uses the caller's κ and keeps its original Z/i/p data. -/
def cofibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    FunctorialFactorizationData (cofibrations (EnrichedFunctorCat V A))
      (trivialFibrations (EnrichedFunctorCat V A)) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  let _ : (generators (A := A) d.I).IsCardinalForSmallObjectArgument κ :=
    generators_isCardinalForSmallObjectArgument d.I QI hI hSourceI
  have hRight : trivialFibrations (EnrichedFunctorCat V A) =
      (generators (A := A) d.I).rlp := by
    rw [trivialFibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells,
      EvaluationTransfer.evaluatedGenerators_rlp_eq
        (fun a : A => EnrichedFunctorCat.Free.functor a)
        (fun a : A => EnrichedFunctorCat.evaluation a)
        (fun a => EnrichedFunctorCat.Free.adjunction a) d.I, d.I_rlp]
  exact (SmallObject.functorialFactorizationData (generators (A := A) d.I) κ).ofLE
    (cofibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells).symm.le hRight.symm.le

/-- The explicit J-factorization uses the caller's κ and keeps its original Z/i/p data. -/
def fibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    FunctorialFactorizationData (trivialCofibrations (EnrichedFunctorCat V A))
      (fibrations (EnrichedFunctorCat V A)) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  let _ : (generators (A := A) d.J).IsCardinalForSmallObjectArgument κ :=
    generators_isCardinalForSmallObjectArgument d.J QJ hJ hSourceJ
  exact (SmallObject.functorialFactorizationData (generators (A := A) d.J) κ).ofLE
    (trivialCofibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells).symm.le
    (by change (generators (A := A) d.J).rlp ≤ (generators (A := A) d.J).rlp; exact le_rfl)

/-- The complete I intermediate functor and both natural arrows are the same explicit κ data. -/
theorem cofibrantFactorizationData_fields :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    letI : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    letI : (generators (A := A) d.I).IsCardinalForSmallObjectArgument κ :=
      generators_isCardinalForSmallObjectArgument d.I QI hI hSourceI
    let data := cofibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
    let original := SmallObject.functorialFactorizationData (generators (A := A) d.I) κ
    data.Z = original.Z ∧ data.i = original.i ∧ data.p = original.p := by
  exact ⟨rfl, rfl, rfl⟩

/-- The complete J intermediate functor and both natural arrows are the same explicit κ data. -/
theorem fibrantFactorizationData_fields :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    letI : d.J.IsSmall.{w} := d.J_smallObject.isSmall
    letI : (generators (A := A) d.J).IsCardinalForSmallObjectArgument κ :=
      generators_isCardinalForSmallObjectArgument d.J QJ hJ hSourceJ
    let data := fibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
    let original := SmallObject.functorialFactorizationData (generators (A := A) d.J) κ
    data.Z = original.Z ∧ data.i = original.i ∧ data.p = original.p := by
  exact ⟨rfl, rfl, rfl⟩

/-- The explicit I-factor maps factor the original caller arrow. -/
theorem cofibrantFactorizationData_fac (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := cofibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
    data.i.app f ≫ data.p.app f = f.hom := by
  exact (cofibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells).fac_app

/-- The explicit J-factor maps factor the original caller arrow. -/
theorem fibrantFactorizationData_fac (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := fibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells
    data.i.app f ≫ data.p.app f = f.hom := by
  exact (fibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells).fac_app

/-- Both returned functorial weak-factorization systems admit the explicit same-κ data. -/
theorem functorialFactorizations :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    HasFunctorialFactorization (cofibrations (EnrichedFunctorCat V A))
        (trivialFibrations (EnrichedFunctorCat V A)) ∧
      HasFunctorialFactorization (trivialCofibrations (EnrichedFunctorCat V A))
        (fibrations (EnrichedFunctorCat V A)) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  constructor
  · exact ⟨⟨cofibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells⟩⟩
  · exact ⟨⟨fibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells⟩⟩

/-- The original free functor and evaluation are Quillen for this same named dictionary. -/
theorem freeAtEvaluation_isQuillenAdjunction (a : A) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (EnrichedFunctorCat.Free.adjunction (V := V) a).IsQuillenAdjunction := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  apply CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    rw [fibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells] at hf
    exact (EvaluationTransfer.evaluationProperty_iff _ (fibrations V) f).mp hf a
  · intro X Y f hf
    rw [trivialFibrations_eq d QI QJ hI hJ hSourceI hSourceJ hCells] at hf
    exact (EvaluationTransfer.evaluationProperty_iff _ (trivialFibrations V) f).mp hf a

end GeneratorCells

end HomotopicalAlgebra.EnrichedProjective
