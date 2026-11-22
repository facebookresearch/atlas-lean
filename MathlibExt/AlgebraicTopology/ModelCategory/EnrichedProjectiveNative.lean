/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.ClosedEmbeddingInstances
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeHornCells
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveGeneratorCells
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHGeneratorSourceSmallness
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHTensorClosedEmbedding

/-!
# Native projective models from the original free-J endpoint

The public construction retains the native base generation data, chosen
realized-generator cardinal and caller bottom. The object index
is in universe zero, as are all three native spectrum operator carriers.
Smallness is derived; no target model, target small-object argument or cell
acyclicity is supplied. Coefficients are the complete native enriched Homs.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MorphismProperty Opposite Topology
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native

private abbrev originalData := PointedCGWH.cofibrantGenerationData.{u, v}
@[instance_reducible]
private def originalBottom : OrderBot realizedGeneratorCardinal.{v}.ord.ToType := inferInstance

private theorem originalI_rlp :
    PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
      trivialFibrations PointedCGWH.{u, v} := originalData.{u, v}.I_rlp

private theorem originalJ_rlp :
    PointedCGWH.realizedHornInclusions.{u, v}.rlp =
      fibrations PointedCGWH.{u, v} := originalData.{u, v}.J_rlp

/-- Closed embeddings of pointed CGWH spaces, detected on the underlying topological map. -/
abbrev closed : MorphismProperty PointedCGWH.{u, v} :=
  TopCat.closedEmbeddings.inverseImage
    (PointedCGWH.pointedToCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v})

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Retain the original six base fields, with eligibility transported to the caller bottom. -/
def generationData : CofibrantGenerationData PointedCGWH.{u, v}
  realizedGeneratorCardinal.{v} where
  I := PointedCGWH.realizedBoundaryInclusions.{u, v}
  J := PointedCGWH.realizedHornInclusions.{u, v}
  I_smallObject := by
    have hB : B = originalBottom.{v} := Subsingleton.elim _ _
    cases hB
    exact originalData.{u, v}.I_smallObject
  J_smallObject := by
    have hB : B = originalBottom.{v} := Subsingleton.elim _ _
    cases hB
    exact originalData.{u, v}.J_smallObject
  I_rlp := by exact originalI_rlp
  J_rlp := by exact originalJ_rlp

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

omit B [EnrichedCategory PointedCGWH.{u, v} A] in
/-- Every native index with objects in universe zero is small in the carrier universe. -/
theorem smallIndex : Small.{v} A := small_zero A

omit B in
/-- The actual CGWH colimits supply pointed colimits in the original cell universe. -/
theorem nativeColimits : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
  infer_instance

omit B in
/-- Original pointed native Hom types are small in their own carrier universe. -/
theorem nativeLocallySmall : LocallySmall.{v} PointedCGWH.{u, v} :=
  CategoryTheory.locallySmall_self _

attribute [local instance] smallIndex nativeColimits nativeLocallySmall

omit B in
/-- Each literal right tensor of a native boundary generator with a full Hom is an
underlying closed embedding. -/
theorem boundaryTensor (a b : A)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : PointedCGWH.realizedBoundaryInclusions.{u, v} f) :
    closed.{u, v} (f ▷ (a ⟶[PointedCGWH.{u, v}] b)) := by
  have hBase := PointedCGWH.realizedBoundaryInclusions.{u, v}.le_llp_rlp f hf
  rw [originalI_rlp, trivialFibrations_llp] at hBase
  let _ : Cofibration f := (HomotopicalAlgebra.cofibration_iff f).2 hBase
  exact PointedCGWH.modelCofibration_whiskerRight_isClosedEmbedding f _

omit B in
/-- Each literal right tensor of a native horn generator with a full Hom is an
underlying closed embedding. -/
theorem hornTensor (a b : A)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : PointedCGWH.realizedHornInclusions.{u, v} f) :
    closed.{u, v} (f ▷ (a ⟶[PointedCGWH.{u, v}] b)) := by
  have hBase := PointedCGWH.realizedHornInclusions.{u, v}.le_llp_rlp f hf
  rw [originalJ_rlp, fibrations_llp] at hBase
  let _ : Cofibration f := (HomotopicalAlgebra.cofibration_iff f).2 hBase.1
  exact PointedCGWH.modelCofibration_whiskerRight_isClosedEmbedding f _

omit B in
/-- The original boundary source Hom preserves the same continuous colimit whose
transitions are underlying closed embeddings. -/
theorem boundarySource
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : PointedCGWH.realizedBoundaryInclusions.{u, v} f)
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v}) [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b), closed.{u, v} (F.map φ)) :
    PreservesColimit F (coyoneda.obj (op X)) := by
  change (CGWH.realizedBoundaryInclusions.{u, v}.strictMap
    (Under.costar CGWH.point)) f at hf
  exact PointedCGWH.realizedBoundarySource_preservesClosedColimit f hf F hF

omit B in
/-- The original horn source Hom preserves the same continuous colimit whose
transitions are underlying closed embeddings. -/
theorem hornSource
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : PointedCGWH.realizedHornInclusions.{u, v} f)
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v}) [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b), closed.{u, v} (F.map φ)) :
    PreservesColimit F (coyoneda.obj (op X)) := by
  change (CGWH.realizedHornInclusions.{u, v}.strictMap
    (Under.costar CGWH.point)) f at hf
  exact PointedCGWH.realizedHornSource_preservesClosedColimit f hf F hF

/-- All six actual free-I eligibility fields follow at the original κ and caller bottom. -/
theorem generatorsI_isCardinalForSmallObjectArgument :
    (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := by
  let _ : PointedCGWH.realizedBoundaryInclusions.{u, v}.IsSmall.{v} :=
    (generationData.{u, v}).I_smallObject.isSmall
  exact generators_isCardinalForSmallObjectArgument (A := A) (κ := realizedGeneratorCardinal.{v})
    PointedCGWH.realizedBoundaryInclusions closed boundaryTensor boundarySource

/-- All six actual free-J eligibility fields follow at the original κ and caller bottom. -/
theorem generatorsJ_isCardinalForSmallObjectArgument :
    (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := by
  let _ : PointedCGWH.realizedHornInclusions.{u, v}.IsSmall.{v} :=
    (generationData.{u, v}).J_smallObject.isSmall
  exact generators_isCardinalForSmallObjectArgument (A := A) (κ := realizedGeneratorCardinal.{v})
    PointedCGWH.realizedHornInclusions closed hornTensor hornSource

private theorem cells (b : A) {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A}
    (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) =>
        (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}).homFamily) f) :
    weakEquivalences PointedCGWH.{u, v} ((EnrichedFunctorCat.evaluation b).map f) :=
  NativeHornCells.endpoint_mem_weakEquivalences b f c

/-- The complete original free-J left class is pointwise weak by the actual mapped retract. -/
theorem evaluated_J_left_le_weakEquivalences :
    (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp ≤
      EvaluationTransfer.evaluationProperty
        (fun b : A => EnrichedFunctorCat.evaluation b) (weakEquivalences PointedCGWH.{u, v}) := by
  let _ : (generators (A := A) PointedCGWH.realizedHornInclusions.{u,
    v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := generatorsJ_isCardinalForSmallObjectArgument
  intro X Y f hf
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun b : A => EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) b)
    (weakEquivalences PointedCGWH.{u, v}) f).2
  intro b
  exact (rlp_llp_le_inverseImage_of_cardinal_cells
    (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v})
    (weakEquivalences PointedCGWH.{u, v}) (EnrichedFunctorCat.evaluation b)
      realizedGeneratorCardinal.{v}
    (cells b)) f hf

/-- The native projective model is the shared factory applied to proved original inputs. -/
@[instance_reducible]
def modelCategory : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  modelCategoryOfGeneratorCells (generationData.{u, v}) closed closed
    boundaryTensor hornTensor boundarySource hornSource (by exact cells)

/-- Weak equivalences are detected on the complete original enriched evaluations. -/
theorem weakEquivalences_eq :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) =
      EvaluationTransfer.evaluationProperty
        (fun b : A => EnrichedFunctorCat.evaluation b) (weakEquivalences PointedCGWH.{u, v}) :=
  GeneratorCells.weakEquivalences_eq (generationData.{u, v}) closed closed
    boundaryTensor hornTensor boundarySource hornSource (by exact cells)

/-- Cofibrations are the complete left class of the literal free boundary family. -/
theorem cofibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) =
      (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp :=
  GeneratorCells.cofibrations_eq (generationData.{u, v}) closed closed
    boundaryTensor hornTensor boundarySource hornSource (by exact cells)

/-- Fibrations are the original pointwise native fibration class. -/
theorem fibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) =
      EvaluationTransfer.evaluationProperty
        (fun b : A => EnrichedFunctorCat.evaluation b) (fibrations PointedCGWH.{u, v}) :=
  GeneratorCells.fibrations_eq (generationData.{u, v}) closed closed
    boundaryTensor hornTensor boundarySource hornSource (by exact cells)

/-- Trivial fibrations are the original pointwise native intersection class. -/
theorem trivialFibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) =
      EvaluationTransfer.evaluationProperty
        (fun b : A => EnrichedFunctorCat.evaluation b) (trivialFibrations PointedCGWH.{u, v}) :=
  GeneratorCells.trivialFibrations_eq (generationData.{u, v}) closed closed
    boundaryTensor hornTensor boundarySource hornSource (by exact cells)

/-- Trivial cofibrations are the full left class of the unchanged literal free horn family. -/
theorem trivialCofibrations_eq :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A) =
      (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp :=
  GeneratorCells.trivialCofibrations_eq (generationData.{u, v}) closed closed
    boundaryTensor hornTensor boundarySource hornSource (by exact cells)

/-- The original κ free-I factorization with unchanged intermediate functor and maps. -/
def cofibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    FunctorialFactorizationData (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  GeneratorCells.cofibrantFactorizationData (generationData.{u, v}) closed closed
    boundaryTensor hornTensor boundarySource hornSource (by exact cells)

/-- The original κ free-J factorization with unchanged intermediate functor and maps. -/
def fibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    FunctorialFactorizationData (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  GeneratorCells.fibrantFactorizationData (generationData.{u, v}) closed closed
    boundaryTensor hornTensor boundarySource hornSource (by exact cells)

/-- Whole free-I Z/i/p data is exactly the original small-object data at the supplied κ. -/
theorem cofibrantFactorizationData_fields :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    letI : (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := generatorsI_isCardinalForSmallObjectArgument
    let data := cofibrantFactorizationData (A := A)
    let original := SmallObject.functorialFactorizationData
      (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v})
        realizedGeneratorCardinal.{v}
    data.Z = original.Z ∧ data.i = original.i ∧ data.p = original.p := by
  exact ⟨rfl, rfl, rfl⟩

/-- Whole free-J Z/i/p data is exactly the original small-object data at the supplied κ. -/
theorem fibrantFactorizationData_fields :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    letI : (generators (A := A) PointedCGWH.realizedHornInclusions.{u,
      v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := generatorsJ_isCardinalForSmallObjectArgument
    let data := fibrantFactorizationData (A := A)
    let original := SmallObject.functorialFactorizationData
      (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}) realizedGeneratorCardinal.{v}
    data.Z = original.Z ∧ data.i = original.i ∧ data.p = original.p := by
  exact ⟨rfl, rfl, rfl⟩

/-- The original free-I maps factor the same caller arrow. -/
theorem cofibrantFactorizationData_fac (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    (cofibrantFactorizationData (A := A)).i.app f ≫
      (cofibrantFactorizationData (A := A)).p.app f = f.hom :=
  (cofibrantFactorizationData (A := A)).fac_app

/-- The original free-J maps factor the same caller arrow. -/
theorem fibrantFactorizationData_fac (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    (fibrantFactorizationData (A := A)).i.app f ≫
      (fibrantFactorizationData (A := A)).p.app f = f.hom :=
  (fibrantFactorizationData (A := A)).fac_app

/-- Both actual weak-factorization systems use the explicit original κ data. -/
theorem functorialFactorizations :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    HasFunctorialFactorization (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A))
        (trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)) ∧
      HasFunctorialFactorization (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A))
        (fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  GeneratorCells.functorialFactorizations (generationData.{u, v}) closed closed
    boundaryTensor hornTensor boundarySource hornSource (by exact cells)

/-- The original native cofibrant factorization is available for the actual
model dictionary, with the caller's same bottom and original generating data. -/
instance nativeCofibrationsHasFunctorialFactorization :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    HasFunctorialFactorization (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  (functorialFactorizations (A := A)).1

/-- The original native fibrant factorization is available for the same
model dictionary and both original source-derived factor records. -/
instance nativeTrivialCofibrationsHasFunctorialFactorization :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    HasFunctorialFactorization (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  (functorialFactorizations (A := A)).2

/-- The original free/evaluation adjunction is Quillen for this same native model. -/
theorem freeAtEvaluation_isQuillenAdjunction (a : A) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
  GeneratorCells.freeAtEvaluation_isQuillenAdjunction
    (generationData.{u, v}) closed closed boundaryTensor hornTensor boundarySource hornSource
      (by exact cells) a

end HomotopicalAlgebra.EnrichedProjective.Native
