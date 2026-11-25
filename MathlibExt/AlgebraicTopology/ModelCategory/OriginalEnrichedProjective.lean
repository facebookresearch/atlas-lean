/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveGeneratorCells.Data
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective.LevelCofibrations
public import MathlibExt.CategoryTheory.Enriched.ExternalTensorMappingEndAdjunction

/-!
# Original enriched projective models with their existing generated factors

The source data below are the original coefficient generators, their Hom
tensors, and their actual source-colimit witnesses. The cell-model factory
and its full fixed-cardinal factors are reused on exactly the original
projective model. The extra cellular acyclicity is derived here and is not
an input model dictionary.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe w uA uV vV

open CategoryTheory Limits MorphismProperty Opposite MonoidalCategory

namespace HomotopicalAlgebra.OriginalEnrichedProjective

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- Exact source hypotheses for the original enriched projective factory. -/
structure SourceConditions (d : CofibrantGenerationData V κ) where
  I_tensor : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
    d.I f → cofibrations V (f ▷ (a ⟶[V] b))
  J_tensor : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
    d.J f → trivialCofibrations V (f ▷ (a ⟶[V] b))
  I_source : ∀ {X Y : V} (f : X ⟶ Y), d.I f →
    ∀ (F : κ.ord.ToType ⥤ V) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), cofibrations V (F.map φ)) →
        PreservesColimit F (coyoneda.obj (op X))
  J_source : ∀ {X Y : V} (f : X ⟶ Y), d.J f →
    ∀ (F : κ.ord.ToType ⥤ V) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), trivialCofibrations V (F.map φ)) →
        PreservesColimit F (coyoneda.obj (op X))

local instance cofibrations_coproducts : (cofibrations V).IsStableUnderCoproducts.{w} :=
  IsStableUnderCoproducts.of_llp_eq (cofibrations V) (trivialFibrations V)
    (trivialFibrations_llp V)

local instance trivialCofibrations_coproducts :
    (trivialCofibrations V).IsStableUnderCoproducts.{w} :=
  IsStableUnderCoproducts.of_llp_eq (trivialCofibrations V) (fibrations V)
    (fibrations_llp V)

local instance cofibrations_transfinite :
    (cofibrations V).IsStableUnderTransfiniteComposition.{w} := by
  rw [← trivialFibrations_llp V]
  infer_instance

local instance trivialCofibrations_transfinite :
    (trivialCofibrations V).IsStableUnderTransfiniteComposition.{w} := by
  rw [← fibrations_llp V]
  infer_instance

variable [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]
  (d : CofibrantGenerationData V κ) (s : SourceConditions (A := A) d)

include s in
/-- Original J Hom-tensor cofibrations derive weak evaluation of the entire J cell complex. -/
theorem J_cells_weak (b : A) {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y)
    (c : RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => (EnrichedProjective.generators (A := A) d.J).homFamily) f) :
    weakEquivalences V ((EnrichedFunctorCat.evaluation b).map f) := by
  let P := EnrichedProjective.generators (A := A) d.J
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  let _ : P.IsCardinalForSmallObjectArgument κ :=
    EnrichedProjective.generators_isCardinalForSmallObjectArgument d.J
      (trivialCofibrations V) s.J_tensor s.J_source
  let t := c.transfiniteCompositionOfShape' (I := P) (fun γ => γ.i.2)
  have hf : P.rlp.llp f :=
    P.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp κ.ord.ToType f t.mem
  have hEval := EnrichedProjective.generatedLeft_le_evaluationProperty
    (A := A) (κ := κ) d.J (trivialCofibrations V) s.J_tensor f hf
  exact ((EvaluationTransfer.evaluationProperty_iff
    (fun a : A => EnrichedFunctorCat.evaluation a) (trivialCofibrations V) f).mp hEval b).2

/-- The existing generator-cell model is literally the original enriched projective model. -/
theorem cellModel_eq_original :
    EnrichedProjective.modelCategoryOfGeneratorCells d
      (cofibrations V) (trivialCofibrations V) s.I_tensor s.J_tensor
      s.I_source s.J_source (J_cells_weak d s) =
    EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source := rfl

/-- Reuse the complete existing generation record on that same original model. -/
def generationData :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    CofibrantGenerationData (EnrichedFunctorCat V A) κ :=
  EnrichedProjective.GeneratorCells.generationData d (cofibrations V) (trivialCofibrations V)
    s.I_tensor s.J_tensor s.I_source s.J_source (J_cells_weak d s)

/-- The complete original first fixed-cardinal factor is reused without choosing new maps. -/
def cofibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    FunctorialFactorizationData (cofibrations (EnrichedFunctorCat V A))
      (trivialFibrations (EnrichedFunctorCat V A)) :=
  EnrichedProjective.GeneratorCells.cofibrantFactorizationData d
    (cofibrations V) (trivialCofibrations V) s.I_tensor s.J_tensor
    s.I_source s.J_source (J_cells_weak d s)

/-- The complete original second fixed-cardinal factor is the existing source construction. -/
def fibrantFactorizationData :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    FunctorialFactorizationData (trivialCofibrations (EnrichedFunctorCat V A))
      (fibrations (EnrichedFunctorCat V A)) :=
  EnrichedProjective.GeneratorCells.fibrantFactorizationData d
    (cofibrations V) (trivialCofibrations V) s.I_tensor s.J_tensor
    s.I_source s.J_source (J_cells_weak d s)

/-- The actual generating families retain every original free-image label. -/
theorem generationData_families :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    (generationData d s).I = EnrichedProjective.generators (A := A) d.I ∧
      (generationData d s).J = EnrichedProjective.generators (A := A) d.J := ⟨rfl, rfl⟩

/-- Generic fixed-generation getters are the same complete original factor records. -/
theorem generationData_factorizations :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    (generationData d s).cofibrantFactorizationData = cofibrantFactorizationData d s ∧
      (generationData d s).fibrantFactorizationData = fibrantFactorizationData d s :=
  ⟨EnrichedProjective.GeneratorCells.generationData_cofibrantFactorizationData d
      (cofibrations V) (trivialCofibrations V) s.I_tensor s.J_tensor
      s.I_source s.J_source (J_cells_weak d s),
    EnrichedProjective.GeneratorCells.generationData_fibrantFactorizationData d
      (cofibrations V) (trivialCofibrations V) s.I_tensor s.J_tensor
      s.I_source s.J_source (J_cells_weak d s)⟩

end HomotopicalAlgebra.OriginalEnrichedProjective
