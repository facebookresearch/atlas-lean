/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveGeneratorCells.Data
public import MathlibExt.CategoryTheory.MorphismProperty.Factorization.GivenDataEquality

/-!
# Actual generation data on the original native enriched model

The original public native eligibility and class equations give generation
at the same realized cardinal and caller bottom. Generic factor getters use
those exact families; their whole record and component functions retain the
existing native values. No base private declaration or new model is used.

The concrete spectrum applications use this record through their enriched
presentation comparisons. These compare each carrier and its Free/evaluation
adjunction with the native enriched category, preserving the original
generator and factorization choices.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MorphismProperty Opposite MonoidalCategory
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.Data

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The original free boundary family gives the same native trivial-fibration class. -/
theorem generatorsI_rlp :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp =
      trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  rw [Native.trivialFibrations_eq]
  rw [EvaluationTransfer.evaluatedGenerators_rlp_eq
    (fun a : A => EnrichedFunctorCat.Free.functor a)
    (fun a : A => EnrichedFunctorCat.evaluation a)
    (fun a => EnrichedFunctorCat.Free.adjunction a)]
  have hBase : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
      trivialFibrations PointedCGWH.{u, v} := by
    let _ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
      instOrderBotToTypeOrdRealizedGeneratorCardinal.{v}
    exact PointedCGWH.cofibrantGenerationData.{u, v}.I_rlp
  rw [hBase]

/-- The original free horn family gives the same native fibration class. -/
theorem generatorsJ_rlp :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}).rlp =
      fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  rw [Native.fibrations_eq]
  rw [EvaluationTransfer.evaluatedGenerators_rlp_eq
    (fun a : A => EnrichedFunctorCat.Free.functor a)
    (fun a : A => EnrichedFunctorCat.evaluation a)
    (fun a => EnrichedFunctorCat.Free.adjunction a)]
  have hBase : PointedCGWH.realizedHornInclusions.{u, v}.rlp =
      fibrations PointedCGWH.{u, v} := by
    let _ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
      instOrderBotToTypeOrdRealizedGeneratorCardinal.{v}
    exact PointedCGWH.cofibrantGenerationData.{u, v}.J_rlp
  rw [hBase]

/-- Return generation on exactly the original native model, realized cardinal and bottom. -/
def generationData :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    CofibrantGenerationData (EnrichedFunctorCat PointedCGWH.{u, v} A)
      realizedGeneratorCardinal.{v} := by
  letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  exact
    { I := generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v}
      J := generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}
      I_smallObject := Native.generatorsI_isCardinalForSmallObjectArgument
      J_smallObject := Native.generatorsJ_isCardinalForSmallObjectArgument
      I_rlp := generatorsI_rlp
      J_rlp := generatorsJ_rlp }

/-- The whole original native free boundary family and every label are retained. -/
theorem generationData_I :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    (generationData (A := A)).I =
      generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v} := rfl

/-- The whole original native free horn family and every label are retained. -/
theorem generationData_J :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    (generationData (A := A)).J =
      generators (A := A) PointedCGWH.realizedHornInclusions.{u, v} := rfl

/-- The complete I eligibility dictionary is the existing original public proof. -/
theorem generationData_I_smallObject :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    (generationData (A := A)).I_smallObject =
      Native.generatorsI_isCardinalForSmallObjectArgument (A := A) := rfl

/-- The complete J eligibility dictionary is the same original public proof. -/
theorem generationData_J_smallObject :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    (generationData (A := A)).J_smallObject =
      Native.generatorsJ_isCardinalForSmallObjectArgument (A := A) := rfl

/-- The original I left class is the actual native cofibration class. -/
theorem generationData_I_left :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    (generationData (A := A)).I.rlp.llp =
      cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  rw [generationData_I]
  exact Native.cofibrations_eq.symm

/-- The original J left class is the actual native trivial-cofibration class. -/
theorem generationData_J_left :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    (generationData (A := A)).J.rlp.llp =
      trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  rw [generationData_J]
  exact Native.trivialCofibrations_eq.symm

/-- All five class equations belong to the same original native model and enriched carrier. -/
theorem generationData_five_classes :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) =
        EvaluationTransfer.evaluationProperty
          (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences PointedCGWH.{u, v}) ∧
      fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) =
        EvaluationTransfer.evaluationProperty
          (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations PointedCGWH.{u, v}) ∧
      trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) =
        EvaluationTransfer.evaluationProperty
          (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations PointedCGWH.{u, v}) ∧
      cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) =
        (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp ∧
      trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) =
        (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp :=
  ⟨Native.weakEquivalences_eq, Native.fibrations_eq, Native.trivialFibrations_eq,
    Native.cofibrations_eq, Native.trivialCofibrations_eq⟩

/-- The generic original I getter is the entire existing native factor value. -/
theorem generationData_cofibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    (generationData (A := A)).cofibrantFactorizationData =
      Native.cofibrantFactorizationData (A := A) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  let _ : (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u,
      v}).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    Native.generatorsI_isCardinalForSmallObjectArgument
  apply FunctorialFactorizationData.eq_of_middle_and_heq_natural_maps
  · exact (generationData (A := A)).cofibrantFactorizationData_Z.trans
      (Native.cofibrantFactorizationData_fields (A := A)).1.symm
  · exact heq_of_eq ((generationData (A := A)).cofibrantFactorizationData_i.trans
      (Native.cofibrantFactorizationData_fields (A := A)).2.1.symm)
  · exact heq_of_eq ((generationData (A := A)).cofibrantFactorizationData_p.trans
      (Native.cofibrantFactorizationData_fields (A := A)).2.2.symm)

/-- The generic original J getter is the entire existing native factor value. -/
theorem generationData_fibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
    (generationData (A := A)).fibrantFactorizationData =
      Native.fibrantFactorizationData (A := A) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  let _ : (generators (A := A) PointedCGWH.realizedHornInclusions.{u,
      v}).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    Native.generatorsJ_isCardinalForSmallObjectArgument
  apply FunctorialFactorizationData.eq_of_middle_and_heq_natural_maps
  · exact (generationData (A := A)).fibrantFactorizationData_Z.trans
      (Native.fibrantFactorizationData_fields (A := A)).1.symm
  · exact heq_of_eq ((generationData (A := A)).fibrantFactorizationData_i.trans
      (Native.fibrantFactorizationData_fields (A := A)).2.1.symm)
  · exact heq_of_eq ((generationData (A := A)).fibrantFactorizationData_p.trans
      (Native.fibrantFactorizationData_fields (A := A)).2.2.symm)

end HomotopicalAlgebra.EnrichedProjective.Native.Data
