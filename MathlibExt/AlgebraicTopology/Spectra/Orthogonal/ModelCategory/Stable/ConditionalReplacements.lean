/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalFactorizations

/-!
# Entire original orthogonal replacements in the conditional model

The original I record on zero-source arrows gives Q, and the entire
paired K record on zero-target arrows gives the native Omega replacement.
Both whole functors, every source action and all four maps retain their
original realized-cardinal small-object definitions. Their model
memberships refer to the same conditional actual native model value.

The unchanged unit and counit squares prove that these original
replacement functions preserve and reflect the actual all-target weak
tests. The original comparison premise remains explicit in the model
views; no stable replacement or localization result is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalReplacements

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom
open PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalFactorizations

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument
  NativeK.generators_isCardinalForSmallObjectArgument

/-- The same original I middle functor on the original zero-source arrows gives Q. -/
def QFunctor (hComparison : ComparisonHomBijections.{u, v} (B := B)) : C.{u, v} ⥤ C.{u, v} :=
  Diagrams.fromZeroArrow ⋙ (IFactorizationData hComparison).Z

/-- The entire original I injection retains its actual zero-source endpoint. -/
def initialToQ (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    (Functor.const C.{u, v}).obj Diagrams.zeroDiagram ⟶ QFunctor hComparison :=
  Functor.whiskerLeft Diagrams.fromZeroArrow (IFactorizationData hComparison).i

/-- The entire original I projection is the same Q counit. -/
def qCounit (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    QFunctor hComparison ⟶ 𝟭 C.{u, v} :=
  Functor.whiskerLeft Diagrams.fromZeroArrow (IFactorizationData hComparison).p

/-- The entire paired K middle functor on original zero-target arrows gives R. -/
def RFunctor (hComparison : ComparisonHomBijections.{u, v} (B := B)) : C.{u, v} ⥤ C.{u, v} :=
  Diagrams.toZeroArrow ⋙ (KFactorizationData hComparison).Z

/-- The same original K injection retains every actual replacement source. -/
def rUnit (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    𝟭 C.{u, v} ⟶ RFunctor hComparison :=
  Functor.whiskerLeft Diagrams.toZeroArrow (KFactorizationData hComparison).i

/-- The same original K projection retains its entire actual zero target. -/
def rToZero (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    RFunctor hComparison ⟶ (Functor.const C.{u, v}).obj Diagrams.zeroDiagram :=
  Functor.whiskerLeft Diagrams.toZeroArrow (KFactorizationData hComparison).p

/-- Both complete original replacements and all four maps are the
unchanged original native functions, with the caller's same bottom. -/
theorem replacement_original_fields (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    QFunctor hComparison = Replacement.cofibrantReplacement (B := B) (A := O) ∧
      initialToQ hComparison = Replacement.initialToCofibrantReplacement (B := B) (A := O) ∧
      qCounit hComparison = Replacement.cofibrantReplacementCounit (B := B) (A := O) ∧
      RFunctor hComparison = NativeK.omegaReplacement orthogonalFamily ∧
      rUnit hComparison = NativeK.omegaReplacementUnit orthogonalFamily ∧
      rToZero hComparison = Functor.whiskerLeft Diagrams.toZeroArrow
        (NativeK.factorizationData orthogonalFamily).p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every original replacement object retains the same literal
zero-arrow input and original realized-generator cardinal. -/
theorem replacement_objects (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (X : C.{u, v}) :
    (QFunctor hComparison).obj X = SmallObject.obj originalI realizedGeneratorCardinal.{v}
        (Diagrams.zeroTo X) ∧
      (RFunctor hComparison).obj X = SmallObject.obj originalK realizedGeneratorCardinal.{v}
        (Diagrams.toZero X) := ⟨rfl, rfl⟩

/-- Every whole native source map retains both original zero-arrow
actions and their actual same-cardinal small-object map functions. -/
theorem replacement_maps (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : C.{u, v}} (f : X ⟶ Y) :
    (QFunctor hComparison).map f = SmallObject.objMap originalI realizedGeneratorCardinal.{v}
        (Diagrams.fromZeroArrow.map f) ∧
      (RFunctor hComparison).map f = SmallObject.objMap originalK realizedGeneratorCardinal.{v}
        (Diagrams.toZeroArrow.map f) := ⟨rfl, rfl⟩

/-- The original Q object is cofibrant in the same conditional actual model. -/
theorem Q_isCofibrant (hComparison : ComparisonHomBijections.{u, v} (B := B)) (X : C.{u, v}) :
    let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
    IsCofibrant ((QFunctor hComparison).obj X) := by
  let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
  change IsCofibrant ((QFunctor hComparison).obj X)
  rw [isCofibrant_iff_of_isInitial ((initialToQ hComparison).app X) Diagrams.zeroDiagramIsInitial]
  exact (HomotopicalAlgebra.cofibration_iff _).mpr
    ((IFactorizationData hComparison).hi (Diagrams.fromZeroArrow.obj X))

/-- Its unchanged entire Q counit is a trivial fibration in that same model. -/
theorem qCounit_trivialFibration (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (X : C.{u, v}) :
    let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
    trivialFibrations C.{u, v} ((qCounit hComparison).app X) :=
  (IFactorizationData hComparison).hp (Diagrams.fromZeroArrow.obj X)

/-- Every original full paired Omega condition holds on the same R object. -/
theorem R_isOmega (hComparison : ComparisonHomBijections.{u, v} (B := B)) (X : C.{u, v}) :
    NativeK.IsOmega orthogonalFamily ((RFunctor hComparison).obj X) :=
  NativeK.omegaReplacement_isOmega orthogonalFamily X

/-- The unchanged original K replacement is fibrant in the same conditional actual model. -/
theorem R_isFibrant (hComparison : ComparisonHomBijections.{u, v} (B := B)) (X : C.{u, v}) :
    let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
    IsFibrant ((RFunctor hComparison).obj X) := by
  let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
  exact (ConditionalModel.isFibrant_iff_isOmega hComparison _).mpr (R_isOmega hComparison X)

/-- Its entire original K unit is a trivial cofibration in that same actual model. -/
theorem rUnit_trivialCofibration (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (X : C.{u, v}) :
    let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
    trivialCofibrations C.{u, v} ((rUnit hComparison).app X) :=
  (KFactorizationData hComparison).hi (Diagrams.toZeroArrow.obj X)

/-- The original zero-target projection is a full paired stable fibration. -/
theorem rToZero_fibration (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (X : C.{u, v}) :
    let : ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison
    fibrations C.{u, v} ((rToZero hComparison).app X) :=
  (KFactorizationData hComparison).hp (Diagrams.toZeroArrow.obj X)

/-- Both original replacement weak maps satisfy every actual native Omega Ho test. -/
theorem replacement_weak_tests (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (X : C.{u, v}) :
    stableWeakEquivalences ((qCounit hComparison).app X) ∧
      stableWeakEquivalences ((rUnit hComparison).app X) :=
  ⟨(NativeStableModels.qCounit_stableTrivialFibration X).2,
    (NativeStableModels.rUnit_stableTrivialCofibration X).2⟩

/-- Both entire original replacement records factor their unchanged actual zero arrows. -/
theorem replacement_fac (hComparison : ComparisonHomBijections.{u, v} (B := B)) (X : C.{u, v}) :
    (initialToQ hComparison).app X ≫ (qCounit hComparison).app X = Diagrams.zeroTo X ∧
      (rUnit hComparison).app X ≫ (rToZero hComparison).app X = Diagrams.toZero X :=
  ⟨(IFactorizationData hComparison).fac_app, (KFactorizationData hComparison).fac_app⟩

/-- Every actual original source map retains both full unit and counit naturality squares. -/
theorem replacement_naturality (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : C.{u, v}} (f : X ⟶ Y) :
    (QFunctor hComparison).map f ≫ (qCounit hComparison).app Y =
        (qCounit hComparison).app X ≫ f ∧
      f ≫ (rUnit hComparison).app Y =
        (rUnit hComparison).app X ≫ (RFunctor hComparison).map f :=
  ⟨(qCounit hComparison).naturality f, (rUnit hComparison).naturality f⟩

/-- The original Q counit square and all-target two-out-of-three law
show that the same full original Q map preserves and reflects weak tests. -/
theorem Q_map_weak_iff (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : C.{u, v}} (f : X ⟶ Y) :
    stableWeakEquivalences ((QFunctor hComparison).map f) ↔ stableWeakEquivalences f := by
  have hX := (replacement_weak_tests hComparison X).1
  have hY := (replacement_weak_tests hComparison Y).1
  have hn := (replacement_naturality hComparison f).1
  constructor
  · intro hf
    have h := stableWeakEquivalences.comp_mem _ _ hf hY
    rw [hn] at h
    exact stableWeakEquivalences.of_precomp _ _ hX h
  · intro hf
    have h := stableWeakEquivalences.comp_mem _ _ hX hf
    rw [← hn] at h
    exact stableWeakEquivalences.of_postcomp _ _ hY h

/-- The original paired K unit square gives the same preservation and
reflection law for every full original R map, on arbitrary endpoints. -/
theorem R_map_weak_iff (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : C.{u, v}} (f : X ⟶ Y) :
    stableWeakEquivalences ((RFunctor hComparison).map f) ↔ stableWeakEquivalences f := by
  have hX := (replacement_weak_tests hComparison X).2
  have hY := (replacement_weak_tests hComparison Y).2
  have hn := (replacement_naturality hComparison f).2
  constructor
  · intro hf
    have h := stableWeakEquivalences.comp_mem _ _ hX hf
    rw [← hn] at h
    exact stableWeakEquivalences.of_postcomp _ _ hY h
  · intro hf
    have h := stableWeakEquivalences.comp_mem _ _ hf hY
    rw [hn] at h
    exact stableWeakEquivalences.of_precomp _ _ hX h

end PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalReplacements
