/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative

/-!
# Native projective construction at the original generator ordinal

This convenience interface fixes the original native generator ordinal once.
The caller-bottom factory remains available, and the returned model record is
proved equal to that factory under every caller bottom. The two explicit
factorization data retain the whole original same-cardinal small-object data.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.Construction

/-- The original native ordinal's bottom, selected before any caller-bottom binder. -/
@[instance_reducible]
def generatorOrderBot : OrderBot realizedGeneratorCardinal.{v}.ord.ToType := inferInstance

attribute [local instance] generatorOrderBot

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- Construct the native projective model using the original native ordinal. -/
@[instance_reducible]
def modelCategory : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Native.modelCategory

/-- The literal original free-I family is eligible at the fixed original cardinal. -/
theorem generatorsI_isCardinalForSmallObjectArgument :
    letI : OrderBot realizedGeneratorCardinal.{v}.ord.ToType := generatorOrderBot
    (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := Native.generatorsI_isCardinalForSmallObjectArgument

/-- The literal original free-J family is eligible at the fixed original cardinal. -/
theorem generatorsJ_isCardinalForSmallObjectArgument :
    letI : OrderBot realizedGeneratorCardinal.{v}.ord.ToType := generatorOrderBot
    (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := Native.generatorsJ_isCardinalForSmallObjectArgument

/-- The full original free-J left class is pointwise weak. -/
theorem evaluated_J_left_le_weakEquivalences :
    (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp ≤
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences PointedCGWH.{u, v}) :=
  Native.evaluated_J_left_le_weakEquivalences

/-- The returned weak class is the complete native evaluation class. -/
theorem weakEquivalences_eq :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences PointedCGWH.{u, v}) :=
  Native.weakEquivalences_eq

/-- The returned cofibration class uses the entire literal free-I family. -/
theorem cofibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) =
      (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp :=
  Native.cofibrations_eq

/-- The returned fibration class is the complete native evaluation class. -/
theorem fibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations PointedCGWH.{u, v}) :=
  Native.fibrations_eq

/-- The returned trivial-fibration class is evaluated on all native objects. -/
theorem trivialFibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations PointedCGWH.{u, v}) :=
  Native.trivialFibrations_eq

/-- The returned trivial-cofibration class uses the entire literal free-J family. -/
theorem trivialCofibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) =
      (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp :=
  Native.trivialCofibrations_eq

/-- The original same-cardinal free-I functorial factorization data. -/
def cofibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    FunctorialFactorizationData (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  Native.cofibrantFactorizationData

/-- The original same-cardinal free-J functorial factorization data. -/
def fibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    FunctorialFactorizationData (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  Native.fibrantFactorizationData

/-- The entire free-I intermediate functor and both natural arrows are original. -/
theorem cofibrantFactorizationData_fields :
    letI : OrderBot realizedGeneratorCardinal.{v}.ord.ToType := generatorOrderBot
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    letI : (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := generatorsI_isCardinalForSmallObjectArgument
    let data := cofibrantFactorizationData (A := A)
    let original := SmallObject.functorialFactorizationData
      (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v})
        realizedGeneratorCardinal.{v}
    data.Z = original.Z ∧ data.i = original.i ∧ data.p = original.p :=
  Native.cofibrantFactorizationData_fields

/-- The entire free-J intermediate functor and both natural arrows are original. -/
theorem fibrantFactorizationData_fields :
    letI : OrderBot realizedGeneratorCardinal.{v}.ord.ToType := generatorOrderBot
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    letI : (generators (A := A) PointedCGWH.realizedHornInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := generatorsJ_isCardinalForSmallObjectArgument
    let data := fibrantFactorizationData (A := A)
    let original := SmallObject.functorialFactorizationData
      (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}) realizedGeneratorCardinal.{v}
    data.Z = original.Z ∧ data.i = original.i ∧ data.p = original.p :=
  Native.fibrantFactorizationData_fields

/-- Every free-I intermediate map is the complete original map of the caller's square. -/
theorem cofibrantFactorizationData_Z_map
    {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (φ : f ⟶ g) :
    letI : OrderBot realizedGeneratorCardinal.{v}.ord.ToType := generatorOrderBot
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    letI : (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := generatorsI_isCardinalForSmallObjectArgument
    (cofibrantFactorizationData (A := A)).Z.map φ =
      SmallObject.objMap (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v})
        realizedGeneratorCardinal.{v} φ := by
  rfl

/-- Every free-J intermediate map is the complete original map of the caller's square. -/
theorem fibrantFactorizationData_Z_map
    {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (φ : f ⟶ g) :
    letI : OrderBot realizedGeneratorCardinal.{v}.ord.ToType := generatorOrderBot
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    letI : (generators (A := A) PointedCGWH.realizedHornInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := generatorsJ_isCardinalForSmallObjectArgument
    (fibrantFactorizationData (A := A)).Z.map φ =
      SmallObject.objMap (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v})
        realizedGeneratorCardinal.{v} φ := by
  rfl

/-- The original free-I natural arrows factor the same caller arrow. -/
theorem cofibrantFactorizationData_fac (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    (cofibrantFactorizationData (A := A)).i.app f ≫
      (cofibrantFactorizationData (A := A)).p.app f = f.hom :=
  Native.cofibrantFactorizationData_fac f

/-- The original free-J natural arrows factor the same caller arrow. -/
theorem fibrantFactorizationData_fac (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    (fibrantFactorizationData (A := A)).i.app f ≫
      (fibrantFactorizationData (A := A)).p.app f = f.hom :=
  Native.fibrantFactorizationData_fac f

/-- Both returned weak-factorization systems use the explicit original cardinal data. -/
theorem functorialFactorizations :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    HasFunctorialFactorization (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A))
        (trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)) ∧
      HasFunctorialFactorization (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A))
        (fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  Native.functorialFactorizations

/-- The actual free/evaluation adjunction is Quillen for the returned native model. -/
theorem freeAtEvaluation_isQuillenAdjunction (a : A) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
  Native.freeAtEvaluation_isQuillenAdjunction a

/-- The convenience constructor agrees with the original factory at every caller bottom. -/
theorem modelCategory_eq_native [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] :
    modelCategory (A := A) = Native.modelCategory (B := B) (A := A) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

end HomotopicalAlgebra.EnrichedProjective.Native.Construction
