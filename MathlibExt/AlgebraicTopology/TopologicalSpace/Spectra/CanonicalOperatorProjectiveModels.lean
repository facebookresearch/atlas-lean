/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeConstruction
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SphereOperatorCategory
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.NativeOperatorIndex

/-!
# Canonical symmetric and orthogonal spectrum level models

The full native operator indices give the genuine spectrum functor carriers.
The original native factory, all five model classes, both complete same-cardinal
factorizations and their maps, and actual free/evaluation adjunctions are retained.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory

attribute [local instance] Native.Construction.generatorOrderBot

namespace PointedCGWH.Spectra.Symmetric

/-- The genuine native functor carrier on the full original symmetric operator index. -/
abbrev Spectrum := EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

/-- The canonical level model is the original native factory on this same carrier. -/
@[instance_reducible]
def levelModel : ModelCategory Spectrum.{u, v} :=
  Native.Construction.modelCategory (A := PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- The entire weak class is the original pointwise native weak class. -/
theorem levelModel_weakEquivalences :
    levelModel.{u, v}.categoryWithWeakEquivalences.weakEquivalences =
      EvaluationTransfer.evaluationProperty
        (fun a : PointedCGWH.SymmetricOperatorIndex.{u, v} => EnrichedFunctorCat.evaluation a)
        (weakEquivalences PointedCGWH.{u, v}) :=
  Native.Construction.weakEquivalences_eq

/-- The entire fibration class is the original pointwise native fibration class. -/
theorem levelModel_fibrations :
    levelModel.{u, v}.categoryWithFibrations.fibrations =
      EvaluationTransfer.evaluationProperty
        (fun a : PointedCGWH.SymmetricOperatorIndex.{u, v} => EnrichedFunctorCat.evaluation a)
        (fibrations PointedCGWH.{u, v}) :=
  Native.Construction.fibrations_eq

/-- Cofibrations use exactly the original full free boundary family. -/
theorem levelModel_cofibrations :
    levelModel.{u, v}.categoryWithCofibrations.cofibrations =
      (generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
        PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp :=
  Native.Construction.cofibrations_eq

/-- The entire trivial-fibration class is the original pointwise intersection. -/
theorem levelModel_trivialFibrations :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    trivialFibrations Spectrum.{u, v} =
      EvaluationTransfer.evaluationProperty
        (fun a : PointedCGWH.SymmetricOperatorIndex.{u, v} => EnrichedFunctorCat.evaluation a)
        (trivialFibrations PointedCGWH.{u, v}) :=
  Native.Construction.trivialFibrations_eq

/-- Trivial cofibrations use exactly the original full free horn family. -/
theorem levelModel_trivialCofibrations :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    trivialCofibrations Spectrum.{u, v} =
      (generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
        PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp :=
  Native.Construction.trivialCofibrations_eq

/-- The original same-cardinal free-I factorization value. -/
def cofibrantFactorizationData :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    FunctorialFactorizationData (cofibrations Spectrum.{u, v})
      (trivialFibrations Spectrum.{u, v}) :=
  Native.Construction.cofibrantFactorizationData

/-- The original same-cardinal free-J factorization value. -/
def fibrantFactorizationData :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    FunctorialFactorizationData (trivialCofibrations Spectrum.{u, v})
      (fibrations Spectrum.{u, v}) :=
  Native.Construction.fibrantFactorizationData

/-- The whole original free-I intermediate functor and both natural arrows are unchanged. -/
theorem cofibrantFactorizationData_fields :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    letI : (generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
      PointedCGWH.realizedBoundaryInclusions.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} :=
      Native.Construction.generatorsI_isCardinalForSmallObjectArgument
    let data := cofibrantFactorizationData.{u, v}
    let original := SmallObject.functorialFactorizationData
      (generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
        PointedCGWH.realizedBoundaryInclusions.{u, v})
      realizedGeneratorCardinal.{v}
    data.Z = original.Z ∧ data.i = original.i ∧ data.p = original.p :=
  Native.Construction.cofibrantFactorizationData_fields

/-- The whole original free-J intermediate functor and both natural arrows are unchanged. -/
theorem fibrantFactorizationData_fields :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    letI : (generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
      PointedCGWH.realizedHornInclusions.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} :=
      Native.Construction.generatorsJ_isCardinalForSmallObjectArgument
    let data := fibrantFactorizationData.{u, v}
    let original := SmallObject.functorialFactorizationData
      (generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
        PointedCGWH.realizedHornInclusions.{u, v})
      realizedGeneratorCardinal.{v}
    data.Z = original.Z ∧ data.i = original.i ∧ data.p = original.p :=
  Native.Construction.fibrantFactorizationData_fields

/-- Every original free-I intermediate map is the map of the same caller square. -/
theorem cofibrantFactorizationData_Z_map
    {f g : Arrow Spectrum.{u, v}} (φ : f ⟶ g) :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    letI : (generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
      PointedCGWH.realizedBoundaryInclusions.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} :=
      Native.Construction.generatorsI_isCardinalForSmallObjectArgument
    cofibrantFactorizationData.{u, v}.Z.map φ =
      SmallObject.objMap
        (generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
          PointedCGWH.realizedBoundaryInclusions.{u, v})
        realizedGeneratorCardinal.{v} φ :=
  Native.Construction.cofibrantFactorizationData_Z_map φ

/-- Every original free-J intermediate map is the map of the same caller square. -/
theorem fibrantFactorizationData_Z_map
    {f g : Arrow Spectrum.{u, v}} (φ : f ⟶ g) :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    letI : (generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
      PointedCGWH.realizedHornInclusions.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} :=
      Native.Construction.generatorsJ_isCardinalForSmallObjectArgument
    fibrantFactorizationData.{u, v}.Z.map φ =
      SmallObject.objMap
        (generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
          PointedCGWH.realizedHornInclusions.{u, v})
        realizedGeneratorCardinal.{v} φ :=
  Native.Construction.fibrantFactorizationData_Z_map φ

/-- The original free-I arrows factor exactly the original caller arrow. -/
theorem cofibrantFactorizationData_fac (f : Arrow Spectrum.{u, v}) :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    cofibrantFactorizationData.{u, v}.i.app f ≫ cofibrantFactorizationData.{u, v}.p.app f = f.hom :=
  Native.Construction.cofibrantFactorizationData_fac f

/-- The original free-J arrows factor exactly the original caller arrow. -/
theorem fibrantFactorizationData_fac (f : Arrow Spectrum.{u, v}) :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    fibrantFactorizationData.{u, v}.i.app f ≫ fibrantFactorizationData.{u, v}.p.app f = f.hom :=
  Native.Construction.fibrantFactorizationData_fac f

/-- The original actual free/evaluation adjunction is Quillen for this same level model. -/
theorem freeAtEvaluation_isQuillenAdjunction (a : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
  Native.Construction.freeAtEvaluation_isQuillenAdjunction a

end PointedCGWH.Spectra.Symmetric

namespace PointedCGWH.Spectra.Orthogonal

/-- The genuine native functor carrier on the full original orthogonal operator index. -/
abbrev Spectrum :=
  EnrichedFunctorCat PointedCGWH.{u, v} CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}

/-- The canonical level model is the original native factory on this same carrier. -/
@[instance_reducible]
def levelModel : ModelCategory Spectrum.{u, v} :=
  Native.Construction.modelCategory (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})

/-- The entire weak class is the original pointwise native weak class. -/
theorem levelModel_weakEquivalences :
    levelModel.{u, v}.categoryWithWeakEquivalences.weakEquivalences =
      EvaluationTransfer.evaluationProperty
        (fun a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v} =>
          EnrichedFunctorCat.evaluation a)
        (weakEquivalences PointedCGWH.{u, v}) :=
  Native.Construction.weakEquivalences_eq

/-- The entire fibration class is the original pointwise native fibration class. -/
theorem levelModel_fibrations :
    levelModel.{u, v}.categoryWithFibrations.fibrations =
      EvaluationTransfer.evaluationProperty
        (fun a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v} =>
          EnrichedFunctorCat.evaluation a)
        (fibrations PointedCGWH.{u, v}) :=
  Native.Construction.fibrations_eq

/-- Cofibrations use exactly the original full free boundary family. -/
theorem levelModel_cofibrations :
    levelModel.{u, v}.categoryWithCofibrations.cofibrations =
      (generators (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
        PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp :=
  Native.Construction.cofibrations_eq

/-- The entire trivial-fibration class is the original pointwise intersection. -/
theorem levelModel_trivialFibrations :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    trivialFibrations Spectrum.{u, v} =
      EvaluationTransfer.evaluationProperty
        (fun a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v} =>
          EnrichedFunctorCat.evaluation a)
        (trivialFibrations PointedCGWH.{u, v}) :=
  Native.Construction.trivialFibrations_eq

/-- Trivial cofibrations use exactly the original full free horn family. -/
theorem levelModel_trivialCofibrations :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    trivialCofibrations Spectrum.{u, v} =
      (generators (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
        PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp :=
  Native.Construction.trivialCofibrations_eq

/-- The original same-cardinal free-I factorization value. -/
def cofibrantFactorizationData :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    FunctorialFactorizationData (cofibrations Spectrum.{u, v})
      (trivialFibrations Spectrum.{u, v}) :=
  Native.Construction.cofibrantFactorizationData

/-- The original same-cardinal free-J factorization value. -/
def fibrantFactorizationData :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    FunctorialFactorizationData (trivialCofibrations Spectrum.{u, v})
      (fibrations Spectrum.{u, v}) :=
  Native.Construction.fibrantFactorizationData

/-- The whole original free-I intermediate functor and both natural arrows are unchanged. -/
theorem cofibrantFactorizationData_fields :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    letI : (generators (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
      PointedCGWH.realizedBoundaryInclusions.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} :=
      Native.Construction.generatorsI_isCardinalForSmallObjectArgument
    let data := cofibrantFactorizationData.{u, v}
    let original := SmallObject.functorialFactorizationData
      (generators (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
        PointedCGWH.realizedBoundaryInclusions.{u, v})
      realizedGeneratorCardinal.{v}
    data.Z = original.Z ∧ data.i = original.i ∧ data.p = original.p :=
  Native.Construction.cofibrantFactorizationData_fields

/-- The whole original free-J intermediate functor and both natural arrows are unchanged. -/
theorem fibrantFactorizationData_fields :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    letI : (generators (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
      PointedCGWH.realizedHornInclusions.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} :=
      Native.Construction.generatorsJ_isCardinalForSmallObjectArgument
    let data := fibrantFactorizationData.{u, v}
    let original := SmallObject.functorialFactorizationData
      (generators (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
        PointedCGWH.realizedHornInclusions.{u, v})
      realizedGeneratorCardinal.{v}
    data.Z = original.Z ∧ data.i = original.i ∧ data.p = original.p :=
  Native.Construction.fibrantFactorizationData_fields

/-- Every original free-I intermediate map is the map of the same caller square. -/
theorem cofibrantFactorizationData_Z_map
    {f g : Arrow Spectrum.{u, v}} (φ : f ⟶ g) :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    letI : (generators (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
      PointedCGWH.realizedBoundaryInclusions.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} :=
      Native.Construction.generatorsI_isCardinalForSmallObjectArgument
    cofibrantFactorizationData.{u, v}.Z.map φ =
      SmallObject.objMap
        (generators (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
          PointedCGWH.realizedBoundaryInclusions.{u, v})
        realizedGeneratorCardinal.{v} φ :=
  Native.Construction.cofibrantFactorizationData_Z_map φ

/-- Every original free-J intermediate map is the map of the same caller square. -/
theorem fibrantFactorizationData_Z_map
    {f g : Arrow Spectrum.{u, v}} (φ : f ⟶ g) :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    letI : (generators (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
      PointedCGWH.realizedHornInclusions.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} :=
      Native.Construction.generatorsJ_isCardinalForSmallObjectArgument
    fibrantFactorizationData.{u, v}.Z.map φ =
      SmallObject.objMap
        (generators (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
          PointedCGWH.realizedHornInclusions.{u, v})
        realizedGeneratorCardinal.{v} φ :=
  Native.Construction.fibrantFactorizationData_Z_map φ

/-- The original free-I arrows factor exactly the original caller arrow. -/
theorem cofibrantFactorizationData_fac (f : Arrow Spectrum.{u, v}) :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    cofibrantFactorizationData.{u, v}.i.app f ≫ cofibrantFactorizationData.{u, v}.p.app f = f.hom :=
  Native.Construction.cofibrantFactorizationData_fac f

/-- The original free-J arrows factor exactly the original caller arrow. -/
theorem fibrantFactorizationData_fac (f : Arrow Spectrum.{u, v}) :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    fibrantFactorizationData.{u, v}.i.app f ≫ fibrantFactorizationData.{u, v}.p.app f = f.hom :=
  Native.Construction.fibrantFactorizationData_fac f

/-- The original actual free/evaluation adjunction is Quillen for this same level model. -/
theorem freeAtEvaluation_isQuillenAdjunction
    (a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :
    letI : ModelCategory Spectrum.{u, v} := levelModel
    (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
  Native.Construction.freeAtEvaluation_isQuillenAdjunction a

end PointedCGWH.Spectra.Orthogonal

namespace PointedCGWH

/-- Public orthogonal spectra are the genuine functors on the original full operator index. -/
abbrev OrthogonalSpectrum := Spectra.Orthogonal.Spectrum.{u, v}

end PointedCGWH
