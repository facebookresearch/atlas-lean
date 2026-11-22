/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeStabilizationMapping
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CofibrantFree
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarCompatibility
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeBoundedSources
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderCofibration
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LevelFibrancy
public import MathlibExt.AlgebraicTopology.ModelCategory.BrownSourceFunctor
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
public import MathlibExt.Topology.Category.PointedCGWH.NativeCurrentMappingSM7
public import MathlibExt.Topology.Category.PointedCGWH.NativeCurrentBrownMapping
public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingSourceFunctor
public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingZeroSource
public import MathlibExt.Topology.Category.TopCat.ClosedEmbeddingRetracts
public import MathlibExt.CategoryTheory.Enriched.ScalarFreeTensor
public import MathlibExt.CategoryTheory.Enriched.FreeGraded
public import MathlibExt.CategoryTheory.Presentable.FiniteSourceClosure
public import MathlibExt.CategoryTheory.SmallObject.Image
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# The original native stabilization-family K factory

The actual native coefficient cofibrancy and continuum bounds derive
fixed-cardinal closed-chain source smallness, the original SOA and WFS,
and full-family Omega replacement. No final K eligibility is supplied.
The original real-boundary/horn generators differ from the disk/cylinder
families in MMSS Definition 6.2; all original native choices are retained.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.MorphismProperty CategoryTheory.EnrichedFunctorCat
open CategoryTheory.BraidedCategory
open Topology
open scoped CGWH.modelCategory MonoidalClosed Cardinal Simplicial

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
private instance originalCardinalRegular : Fact realizedGeneratorCardinal.{v}.IsRegular :=
  ⟨isRegular_realizedGeneratorCardinal⟩

/-- Only actual native source objects, coefficients and their proved size/cofibrancy facts enter. -/
structure NativeStabilizationFamily (I : Type)
    [EnrichedCategory PointedCGWH.{u, v} I] (L : Type) where
  /-- The actual source operator object for each original label. -/
  source : L → I
  /-- The actual target operator object for each original label. -/
  target : L → I
  /-- The original native pointed coefficient for each stabilization map. -/
  coefficient : L → PointedCGWH.{u, v}
  /-- The full original coefficient map into the actual enriched operator Hom. -/
  inclusion : ∀ l : L, coefficient l ⟶ (source l ⟶[PointedCGWH.{u, v}] target l)
  coefficient_cofibrant : ∀ l : L, IsCofibrant (coefficient l)
  coefficient_bound : ∀ l : L, #↥(coefficient l).right ≤ Cardinal.continuum

namespace NativeK

private theorem originalContravariantFactorization
    {C D : Type*} [Category C] [Category D] (F : Cᵒᵖ ⥤ D)
    {X Y Z : C} (j : X ⟶ Y) (r : Y ⟶ Z) (f : X ⟶ Z) (hf : j ≫ r = f) :
    F.map r.op ≫ F.map j.op = F.map f.op := by
  rw [← F.map_comp]
  change F.map (j ≫ r).op = F.map f.op
  rw [hf]

private theorem originalWeakFactorization_iff
    {C : Type*} [Category C] (W : MorphismProperty C) [W.HasTwoOutOfThreeProperty]
    {X Y Z : C} (r : X ⟶ Y) (j : Y ⟶ Z) (f : X ⟶ Z)
    (hfac : r ≫ j = f) (hr : W r) : W j ↔ W f := by
  constructor
  · intro hj
    have h := W.comp_mem r j hr hj
    rwa [hfac] at h
  · intro hf
    apply W.of_precomp r j hr
    rwa [hfac]


open PointedCGWH.EnrichedFunctorMapping PointedCGWH.EnrichedSource
open PointedCGWH.CoefficientCardinal
open HomotopicalAlgebra.EnrichedProjective.Native
open CategoryTheory.EnrichedFunctorCat.ScalarLeibniz

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)

/-- The original native model on this exact full enriched operator carrier. -/
@[instance_reducible]
def levelModel : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  Construction.modelCategory

/-- The entire original freely pointed horn family is retained literally. -/
abbrev levelJ : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  HomotopicalAlgebra.EnrichedProjective.generators (A := I) PointedCGWH.realizedHornInclusions

/-- The entire original freely pointed boundary family is retained literally. -/
abbrev levelI : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  HomotopicalAlgebra.EnrichedProjective.generators (A := I)
    PointedCGWH.realizedBoundaryInclusions

/-- Every original index pair supplies the exact normalized native free arrow. -/
abbrev stabilization (l : L) :=
  CurrentFree.stabilization (s.source l) (s.target l) (s.coefficient l) (s.inclusion l)

/-- The actual current operator action, with all its source and target parameters. -/
abbrev adjoint (l : L) (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  CurrentFree.adjoint (s.source l) (s.target l) (s.coefficient l) (s.inclusion l) X

/-- The Omega condition uses the actual native weak class on every original operator transpose. -/
def IsOmega (X : EnrichedFunctorCat PointedCGWH.{u, v} I) : Prop :=
  ∀ l : L, weakEquivalences PointedCGWH.{u, v} (adjoint s l X)

/-- The original freely pointed finite boundary coefficient, including its original objects. -/
abbrev boundaryMap (m : ℕ) :=
  (Under.costar CGWH.point.{u, v}).map (CGWH.realizedBoundaryInclusion.{v, u} m)

/-- The complete original native mapping cylinder of that same free stabilization arrow. -/
abbrev cylinder (l : L) :=
  PointedCGWH.EnrichedIntervalMappingCylinder.object (CategoryTheory.Arrow.mk (stabilization s l))

/-- The actual second interval endpoint gives the original cofibration factor. -/
abbrev cylinderSource (l : L) :=
  PointedCGWH.EnrichedIntervalMappingCylinder.source (CategoryTheory.Arrow.mk (stabilization s l))

/-- The literal original contraction gives the same mapping-cylinder retraction. -/
abbrev cylinderRetraction (l : L) :=
  PointedCGWH.EnrichedIntervalMappingCylinder.retraction
    (CategoryTheory.Arrow.mk (stabilization s l))

/-- The two original mapping-cylinder factors compose to the original native free map. -/
theorem cylinder_fac (l : L) :
    cylinderSource s l ≫ cylinderRetraction s l = stabilization s l :=
  PointedCGWH.EnrichedIntervalMappingCylinder.fac _

private theorem originalCylinder_mapping_factorization
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (PointedCGWH.NativeMappingSourceFunctor.source E).map
        (PointedCGWH.EnrichedIntervalMappingCylinder.retraction f).op ≫
      (PointedCGWH.NativeMappingSourceFunctor.source E).map
        (PointedCGWH.EnrichedIntervalMappingCylinder.source f).op =
      (PointedCGWH.NativeMappingSourceFunctor.source E).map f.hom.op :=
  originalContravariantFactorization
    (PointedCGWH.NativeMappingSourceFunctor.source E)
    (PointedCGWH.EnrichedIntervalMappingCylinder.source f)
    (PointedCGWH.EnrichedIntervalMappingCylinder.retraction f) f.hom
    (PointedCGWH.EnrichedIntervalMappingCylinder.fac f)

/-- The correlated native scalar boundary/cylinder pushout, retaining both original labels. -/
def generatorSquare (l : L) (m : ℕ) :
    WeightedEndVariance.tensorBifunctor.PushoutObjObj (boundaryMap.{u, v} m)
      (cylinderSource s l) :=
  Functor.PushoutObjObj.ofHasPushout WeightedEndVariance.tensorBifunctor
    (boundaryMap m) (cylinderSource s l)

/-- The literal extra generator retains the original full pushout arrow. -/
abbrev generatorMap (l : L) (m : ℕ) := (generatorSquare s l m).ι

/-- Both original labels remain correlated in the full actual extra family. -/
def additionalGenerators : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  MorphismProperty.ofHoms (fun lm : L × ℕ => generatorMap s lm.1 lm.2)

/-- K is the literal original level horn family and original correlated native maps. -/
def generators : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  levelJ (I := I) ⊔ additionalGenerators s

/-- Membership retains the full original two summands. -/
theorem generators_iff {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    generators s f ↔ levelJ f ∨ additionalGenerators s f :=
  MorphismProperty.sup_iff _ _ _

/-- Each actual correlated source pair belongs to the actual additional family. -/
theorem generatorMap_mem (l : L) (m : ℕ) : additionalGenerators s (generatorMap s l m) :=
  ⟨(l, m)⟩

/-- The original whole level horn family belongs to K without changing any source map. -/
theorem levelJ_le_generators : levelJ.{u, v} (I := I) ≤ generators s := le_sup_left

/-- Lifting against one actual K generator is exactly lifting against its original full corner. -/
theorem generatorMap_lifting_iff (l : L) (m : ℕ)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y) :
    HasLiftingProperty (generatorMap s l m) p ↔
      HasLiftingProperty (boundaryMap m) (PointedCGWH.NativeMappingCorner.square
        (cylinderSource s l) p).π :=
  PointedCGWH.NativeMappingCorner.lifting_iff (generatorSquare s l m)
    (PointedCGWH.NativeMappingCorner.square (cylinderSource s l) p)

/-- The actual complete boundary family detects the original native trivial fibrations. -/
private theorem originalBoundaryRlp : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
    trivialFibrations PointedCGWH.{u, v} :=
  PointedCGWH.cofibrantGenerationData.{u, v}.I_rlp

/-- The actual complete boundary family detects the original native trivial fibrations. -/
theorem boundary_lifting_iff {X Y : PointedCGWH.{u, v}} (p : X ⟶ Y) :
    (∀ m : ℕ, HasLiftingProperty (boundaryMap m) p) ↔
      trivialFibrations PointedCGWH.{u, v} p := by
  constructor
  · intro h
    have hp : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp p := by
      intro A C i hi
      change (CGWH.realizedBoundaryInclusions.{u, v}.strictMap (Under.costar CGWH.point)) i at hi
      cases hi with
      | @map A C i hi =>
        obtain ⟨m⟩ := hi
        exact h m
    rwa [originalBoundaryRlp] at hp
  · intro h m
    have hp : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp p := by
      rwa [originalBoundaryRlp]
    apply hp
    change (CGWH.realizedBoundaryInclusions.{u, v}.strictMap (Under.costar CGWH.point))
      (boundaryMap m)
    exact .map (CGWH.boundary_mem_realizedBoundaryInclusions m)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- Full K lifting retains level fibrations and every original native mapping corner. -/
theorem lifting_iff {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y) :
    (generators s).rlp p ↔
      fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) p ∧
        ∀ l : L, trivialFibrations PointedCGWH.{u, v}
          (PointedCGWH.NativeMappingCorner.square (cylinderSource s l) p).π := by
  constructor
  · intro h
    refine ⟨?_, fun l => (boundary_lifting_iff _).mp (fun m => ?_)⟩
    · have hp : levelJ (I := I).rlp p := by
        intro A C i hi
        exact h i (levelJ_le_generators s _ hi)
      exact hp
    · exact (generatorMap_lifting_iff s l m p).mp
        (h _ ((generators_iff s _).mpr (Or.inr (generatorMap_mem s l m))))
  · rintro ⟨hLevel, hCorners⟩
    intro A C i hi
    rcases (generators_iff s i).mp hi with hJ | hExtra
    · exact hLevel i hJ
    · obtain ⟨⟨l, m⟩⟩ := hExtra
      exact (generatorMap_lifting_iff s l m p).mpr
        ((boundary_lifting_iff _).mpr (hCorners l) m)

/-- The actual original free/evaluation Quillen adjunction supplies cofibrancy of a free source. -/
theorem freeCoefficient_cofibrant (a : I) (T : PointedCGWH.{u, v}) [IsCofibrant T] :
    IsCofibrant (Free.object a T) :=
  HomotopicalAlgebra.EnrichedProjective.Native.freeAt_obj_isCofibrant a T

/-- The actual native sphere coefficient gives the cofibrant original stabilization source. -/
theorem stabilization_source_cofibrant (l : L) :
    IsCofibrant (CategoryTheory.Arrow.mk (stabilization s l)).left := by
  let _ : IsCofibrant (s.coefficient l) := s.coefficient_cofibrant l
  exact freeCoefficient_cofibrant (s.target l) (s.coefficient l)

/-- The original native smash unit gives the cofibrant original stabilization target. -/
theorem stabilization_target_cofibrant (l : L) :
    IsCofibrant (CategoryTheory.Arrow.mk (stabilization s l)).right := by
  let _ : IsCofibrant (𝟙_ PointedCGWH.{u, v}) :=
    PointedCGWH.modelCategory.smashUnit_isCofibrant
  exact freeCoefficient_cofibrant (s.source l) (𝟙_ PointedCGWH.{u, v})

/-- The original second-endpoint cylinder source is an actual native projective cofibration. -/
theorem cylinderSource_cofibration (l : L) : Cofibration (cylinderSource s l) := by
  let _ : IsCofibrant (CategoryTheory.Arrow.mk (stabilization s l)).left :=
    stabilization_source_cofibrant s l
  let _ : IsCofibrant (CategoryTheory.Arrow.mk (stabilization s l)).right :=
    stabilization_target_cofibrant s l
  exact PointedCGWH.EnrichedIntervalMappingCylinderModel.source_cofibration _

/-- The same original mapping-cylinder retraction is weak in the actual level model. -/
theorem cylinderRetraction_weak (l : L) : WeakEquivalence (cylinderRetraction s l) := by
  let _ : IsCofibrant (CategoryTheory.Arrow.mk (stabilization s l)).left :=
    stabilization_source_cofibrant s l
  exact PointedCGWH.EnrichedIntervalMappingCylinderModel.retraction_weakEquivalence _

/-- Each original correlated generator is projectively cofibrant by the actual native scalar SM7. -/
theorem generatorMap_cofibration (l : L) (m : ℕ) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (generatorMap s l m) := by
  have hB : B = Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  let po := generatorSquare s l m
  let oldPo := Functor.PushoutObjObj.transport (by rfl) po
  have hi : cofibrations PointedCGWH.{u, v} (boundaryMap m) := by
    have h := PointedCGWH.realizedBoundaryInclusions.{u, v}.le_llp_rlp
      (boundaryMap m) (.map (CGWH.boundary_mem_realizedBoundaryInclusions m))
    rwa [originalBoundaryRlp, trivialFibrations_llp] at h
  have h := ScalarCompatibility.scalarPushoutProduct_cofibration (boundaryMap m)
    (cylinderSource s l) hi ((HomotopicalAlgebra.cofibration_iff _).mp
      (cylinderSource_cofibration s l)) oldPo
  have hSame : oldPo.ι = po.ι := eq_of_heq
    (Functor.PushoutObjObj.transport_arrow_heq (by rfl) po)
  rwa [hSame] at h

/-- The whole literal K family lies in the native projective cofibrations. -/
theorem generators_le_cofibrations : generators s ≤
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) := by
  intro X Y f hf
  rcases (generators_iff s f).mp hf with hJ | hExtra
  · have h := (levelJ (I := I)).le_llp_rlp f hJ
    rw [← HomotopicalAlgebra.EnrichedProjective.Native.trivialCofibrations_eq] at h
    exact h.1
  · obtain ⟨⟨l, m⟩⟩ := hExtra
    exact generatorMap_cofibration s l m

/-- Every original K-left arrow is projectively cofibrant on arbitrary original sources. -/
theorem left_le_cofibrations : (generators s).rlp.llp ≤
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) := by
  rw [← trivialFibrations_llp]
  intro X Y f hf A C p hp
  apply hf p
  intro U V i hi
  have hc := generators_le_cofibrations s i hi
  rw [← trivialFibrations_llp] at hc
  exact hc p hp

/-- Every original K-right arrow retains its whole original level fibration class. -/
theorem right_le_fibrations : (generators s).rlp ≤
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  fun _ _ _ hp => ((lifting_iff s _).mp hp).1

private abbrev closed := TopCat.closedEmbeddings.inverseImage
  (PointedCGWH.pointedToCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v})

private instance nativeColimits : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
  infer_instance

omit B in
private theorem evaluationContinuous (a : I) :
    PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType
      (evaluation (V := PointedCGWH.{u, v}) a) where
  preservesColimitsOfShape := fun _ _ => by infer_instance

/-- Original free-I cardinal reduction proves closedness at every actual native evaluation. -/
theorem cofibration_component_closedEmbedding
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) f) (a : I) :
    IsClosedEmbedding (ConcreteCategory.hom (component f a).right) := by
  have hB : B = Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  let P := levelI.{u, v} (I := I)
  let Q := closed.{u, v}
  let U := evaluation (V := PointedCGWH.{u, v}) a
  let _ : P.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    HomotopicalAlgebra.EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument
  let _ : PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType U :=
    evaluationContinuous a
  have hP : P ≤ Q.inverseImage U := by
    apply HomotopicalAlgebra.EnrichedProjective.generators_evaluation_le
      PointedCGWH.realizedBoundaryInclusions Q
    intro b c A C i hi
    have hC := PointedCGWH.realizedBoundaryInclusions.{u, v}.le_llp_rlp i hi
    rw [originalBoundaryRlp, trivialFibrations_llp] at hC
    let _ : Cofibration i := (HomotopicalAlgebra.cofibration_iff i).mpr hC
    exact PointedCGWH.modelCofibration_whiskerRight_isClosedEmbedding i _
  have hLeft := rlp_llp_le_inverseImage_of_cardinal_closure P Q U
    realizedGeneratorCardinal.{v} hP
  have hf' : P.rlp.llp f := by
    rwa [HomotopicalAlgebra.EnrichedProjective.Native.cofibrations_eq] at hf
  exact hLeft f hf'

private instance cofibrationsCoprod :
    (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)).IsStableUnderCoproducts.{v} :=
  IsStableUnderCoproducts.of_llp_eq _ _ (trivialFibrations_llp _)

private instance cofibrationsTransfinite :
    IsStableUnderTransfiniteComposition.{v}
      (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)) := by
  rw [← trivialFibrations_llp]
  infer_instance

private instance identityContinuous :
    PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType
      (𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I)) where
  preservesColimitsOfShape := fun _ _ => by infer_instance

/-- Every actual endpoint of an original-cardinal K-cell complex is a native cofibration. -/
theorem cellEndpoint_cofibration
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => (generators s).homFamily) f) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) f := by
  have h : generators s ≤
      (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)).inverseImage (𝟭 _) :=
    generators_le_cofibrations s
  exact c.map_mem_of_le (𝟭 _) (generators s) (cofibrations _) h

/-- Every entire transition in that same original K-cell diagram is a native cofibration. -/
theorem cellTransition_cofibration
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => (generators s).homFamily) f)
    {a b : realizedGeneratorCardinal.{v}.ord.ToType} (φ : a ⟶ b) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (c.F.map φ) := by
  have h : generators s ≤
      (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)).inverseImage (𝟭 _) :=
    generators_le_cofibrations s
  exact c.map_map_mem_of_le (𝟭 _) (generators s) (cofibrations _) h φ

/-- Every full native evaluation of each original-cardinal K transition is closed. -/
theorem cellTransition_closedEmbedding
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => (generators s).homFamily) f)
    {a b : realizedGeneratorCardinal.{v}.ord.ToType} (φ : a ⟶ b) (i : I) :
    IsClosedEmbedding (ConcreteCategory.hom (component (c.F.map φ) i).right) :=
  cofibration_component_closedEmbedding _ (cellTransition_cofibration s f c φ) i

omit B in
/-- The original finite realization source is transported by its actual finite/general Iso. -/
theorem finiteCostarOfFinite_mk_le (T : SSet.{v}) [T.Finite] :
    #↥(((Under.costar CGWH.point.{u, v}).obj (SSet.toCGWHOfFinite T)).right) ≤
      Cardinal.continuum := by
  let e : ((Under.costar CGWH.point.{u, v}).obj (SSet.toCGWH.obj T)).right ≅
      ((Under.costar CGWH.point.{u, v}).obj (SSet.toCGWHOfFinite T)).right :=
    PointedCGWH.pointedToCGWH.mapIso
      ((Under.costar CGWH.point.{u, v}).mapIso (CGWH.finiteRealizationIso T))
  rw [← Cardinal.mk_congr (CGWH.homeoOfIso e).toEquiv]
  exact finiteCostar_mk_le T

omit B in
/-- The literal boundary source has its original finite realization carrier bound. -/
theorem boundary_source_mk_le (m : ℕ) :
    #↥(CategoryTheory.Arrow.mk (boundaryMap.{u, v} m)).left.right ≤ Cardinal.continuum :=
  finiteCostarOfFinite_mk_le (SSet.boundary.{v} m)

omit B in
/-- The literal boundary target has the same original finite carrier bound. -/
theorem boundary_target_mk_le (m : ℕ) :
    #↥(CategoryTheory.Arrow.mk (boundaryMap.{u, v} m)).right.right ≤ Cardinal.continuum :=
  finiteCostarOfFinite_mk_le (Δ[m] : SSet.{v})

omit B in
/-- The actual scalar interval is the original freely pointed finite one-simplex. -/
theorem interval_mk_le :
    #↥(PointedCGWH.IntervalCoefficient.interval.{u, v}.right) ≤ Cardinal.continuum :=
  finiteCostar_mk_le (Δ[1] : SSet.{v})

omit B in
private theorem sourceOfPushout
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    {Z X Y P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    {f : Z ⟶ X} {g : Z ⟶ Y} {i : X ⟶ P} {j : Y ⟶ P}
    (sq : IsPushout f g i j)
    (hZ : PreservesColimit E (coyoneda.obj (Opposite.op Z)))
    (hX : PreservesColimit E (coyoneda.obj (Opposite.op X)))
    (hY : PreservesColimit E (coyoneda.obj (Opposite.op Y))) :
    PreservesColimit E (coyoneda.obj (Opposite.op P)) := by
  refine preservesColimit_coyoneda_of_finiteColimit
    realizedGeneratorCardinal.{v} E sq.cocone sq.isColimit ?_
  intro k
  cases k with
  | none => exact hZ
  | some k =>
    cases k with
    | left => exact hX
    | right => exact hY

/-- The entire scalar stabilization cylinder has source Hom at the original cardinal. -/
theorem scalarCylinder_preservesClosedColimit
    (T : PointedCGWH.{u, v}) (hT : #↥T.right ≤ Cardinal.continuum) (l : L)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op (tensorLeftObject T (cylinder s l)))) := by
  let F := CategoryTheory.Arrow.mk (stabilization s l)
  let U : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} I := EnrichedFunctorCat.tensorLeft T
  let _ : PreservesColimits U := (ScalarLeibniz.adjunction T).leftAdjoint_preservesColimits
  let sq := (IsPushout.of_hasPushout
    (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 F.left) F.hom).map U
  apply sourceOfPushout E sq
  · exact scalarFree_preservesClosedColimit (s.target l) T (s.coefficient l)
      hT (s.coefficient_bound l) E hE
  · exact scalarScalarFree_preservesClosedColimit (s.target l) T
      PointedCGWH.IntervalCoefficient.interval (s.coefficient l)
      hT interval_mk_le (s.coefficient_bound l) E hE
  · exact scalarFree_preservesClosedColimit (s.source l) T
      (𝟙_ PointedCGWH.{u, v}) hT unit_mk_le E hE

/-- The actual correlated K-generator source preserves the supplied original continuous chain. -/
theorem generatorSource_preservesClosedColimit (l : L) (m : ℕ)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E
      (coyoneda.obj (Opposite.op (CategoryTheory.Arrow.mk (generatorMap s l m)).left)) := by
  apply sourceOfPushout E (generatorSquare s l m).isPushout
  · exact scalarFree_preservesClosedColimit (s.target l)
      (CategoryTheory.Arrow.mk (boundaryMap m)).left (s.coefficient l)
      (boundary_source_mk_le m) (s.coefficient_bound l) E hE
  · exact scalarFree_preservesClosedColimit (s.target l)
      (CategoryTheory.Arrow.mk (boundaryMap m)).right (s.coefficient l)
      (boundary_target_mk_le m) (s.coefficient_bound l) E hE
  · exact scalarCylinder_preservesClosedColimit s
      (CategoryTheory.Arrow.mk (boundaryMap m)).left (boundary_source_mk_le m) l E hE

/-- The original generator target retains its genuine source-Hom preservation as well. -/
theorem generatorTarget_preservesClosedColimit (l : L) (m : ℕ)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E
      (coyoneda.obj (Opposite.op (CategoryTheory.Arrow.mk (generatorMap s l m)).right)) :=
  scalarCylinder_preservesClosedColimit s
    (CategoryTheory.Arrow.mk (boundaryMap m)).right (boundary_target_mk_le m) l E hE

omit B in
private theorem originalHornSource_mk_le {A C : PointedCGWH.{u, v}} (f : A ⟶ C)
    (hf : PointedCGWH.realizedHornInclusions f) : #↥A.right ≤ Cardinal.continuum := by
  change (CGWH.realizedHornInclusions.{u, v}.strictMap (Under.costar CGWH.point)) f at hf
  cases hf with
  | @map A C f hf =>
    unfold CGWH.realizedHornInclusions at hf
    rw [MorphismProperty.iSup_iff] at hf
    obtain ⟨n, ⟨i⟩⟩ := hf
    exact finiteCostarOfFinite_mk_le (SSet.horn.{v} (n + 1) i)

/-- Every member of the entire original free-J summand has its actual bounded free source. -/
theorem levelJSource_preservesClosedColimit
    {A C : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : A ⟶ C) (hf : levelJ f)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op A)) := by
  let U : I → PointedCGWH.{u, v} ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I :=
    fun a => Free.functor a
  obtain ⟨q, hq⟩ := (MorphismProperty.adjointFamilyGenerators_iff U
    PointedCGWH.realizedHornInclusions f).mp hf
  let _ : PreservesColimit E (coyoneda.obj (Opposite.op (Free.object q.1 q.2.1.left))) :=
    free_preservesClosedColimit q.1 q.2.1.left (originalHornSource_mk_le _ q.2.2) E hE
  let e : A ≅ Free.object q.1 q.2.1.left := CategoryTheory.Arrow.leftFunc.mapIso (eqToIso hq)
  exact preservesColimit_of_natIso E (coyoneda.mapIso e.op)

/-- Both full original K summands preserve their source Hom on the same supplied chain. -/
theorem generatorsSource_preservesClosedColimit
    {A C : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : A ⟶ C) (hf : generators s f)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op A)) := by
  rcases (generators_iff s f).mp hf with hJ | hExtra
  · exact levelJSource_preservesClosedColimit f hJ E hE
  · obtain ⟨⟨l, m⟩⟩ := hExtra
    exact generatorSource_preservesClosedColimit s l m E hE

/-- Both original K summands are genuinely small at the native index and cell universes. -/
theorem generators_isSmall : (generators s).IsSmall.{v} := by
  let hJ : levelJ (I := I).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    HomotopicalAlgebra.EnrichedProjective.Native.generatorsJ_isCardinalForSmallObjectArgument
  let _ : levelJ (I := I).IsSmall.{v} := hJ.isSmall
  let _ : Small.{v} (L × ℕ) := small_zero _
  let _ : (additionalGenerators s).IsSmall.{v} := by
    unfold additionalGenerators
    infer_instance
  let φ : (levelJ (I := I)).toSet ⊕ (additionalGenerators s).toSet → (generators s).toSet :=
    Sum.elim
      (fun i => ⟨i.1, (generators_iff s _).mpr (Or.inl i.2)⟩)
      (fun i => ⟨i.1, (generators_iff s _).mpr (Or.inr i.2)⟩)
  have hφ : Function.Surjective φ := by
    rintro ⟨f, hf⟩
    rcases (generators_iff s f.hom).mp hf with hJ | hExtra
    · exact ⟨Sum.inl ⟨f, hJ⟩, rfl⟩
    · exact ⟨Sum.inr ⟨f, hExtra⟩, rfl⟩
  exact ⟨small_of_surjective hφ⟩

/-- All original eligibility fields follow at the same regular cardinal and caller bottom. -/
theorem generators_isCardinalForSmallObjectArgument :
    (generators s).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} := by
  let _ : Small.{v} I := small_zero _
  refine { isSmall := generators_isSmall s, preservesColimit := ?_ }
  intro A C X Y i hi f c
  let _ : c.F.IsWellOrderContinuous :=
    c.toTransfiniteCompositionOfShape.isWellOrderContinuous
  exact generatorsSource_preservesClosedColimit s i hi c.F
    (fun a _ _ φ => cellTransition_closedEmbedding s f c φ a)

attribute [local instance] generators_isCardinalForSmallObjectArgument

/-- The actual native K small-object data uses the literal original regular cardinal. -/
def factorizationData : FunctorialFactorizationData (generators s).rlp.llp (generators s).rlp :=
  SmallObject.functorialFactorizationData (generators s) realizedGeneratorCardinal.{v}

/-- The entire middle functor and both natural arrows are the original same-cardinal functions. -/
theorem factorizationData_fields :
    let original := SmallObject.functorialFactorizationData
      (generators s) realizedGeneratorCardinal.{v}
    (factorizationData s).Z = original.Z ∧ (factorizationData s).i = original.i ∧
      (factorizationData s).p = original.p := ⟨rfl, rfl, rfl⟩

/-- Every entire caller Arrow retains the original small-object intermediate object. -/
theorem factorizationData_Z_obj
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (factorizationData s).Z.obj f =
      SmallObject.obj (generators s) realizedGeneratorCardinal.{v} f.hom :=
  rfl

/-- The complete original Arrow map is the original same-cardinal small-object map function. -/
theorem factorizationData_Z_map
    {f g : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : f ⟶ g) :
    (factorizationData s).Z.map φ =
      SmallObject.objMap (generators s) realizedGeneratorCardinal.{v} φ :=
  rfl

/-- The entire original left factor is the original small-object injection function. -/
theorem factorizationData_i_app
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (factorizationData s).i.app f =
      SmallObject.ιObj (generators s) realizedGeneratorCardinal.{v} f.hom :=
  rfl

/-- The entire original right factor is the original small-object projection function. -/
theorem factorizationData_p_app
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (factorizationData s).p.app f =
      SmallObject.πObj (generators s) realizedGeneratorCardinal.{v} f.hom :=
  rfl

/-- The two actual factors compose to the same original caller Arrow. -/
theorem factorizationData_fac (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (factorizationData s).i.app f ≫ (factorizationData s).p.app f = f.hom :=
  (factorizationData s).fac_app

/-- Every full Arrow input keeps the original left naturality square. -/
theorem factorizationData_i_naturality
    {f g : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : f ⟶ g) :
    (factorizationData s).i.app f ≫ (factorizationData s).Z.map φ =
      φ.left ≫ (factorizationData s).i.app g :=
  ((factorizationData s).i.naturality φ).symm

/-- Every full Arrow input keeps the original right naturality square. -/
theorem factorizationData_p_naturality
    {f g : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : f ⟶ g) :
    (factorizationData s).Z.map φ ≫ (factorizationData s).p.app g =
      (factorizationData s).p.app f ≫ φ.right :=
  (factorizationData s).p.naturality φ

/-- Every actual original right factor retains every full native mapping corner. -/
theorem factorizationData_p_corners
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (l : L) :
    trivialFibrations PointedCGWH.{u, v}
      (PointedCGWH.NativeMappingCorner.square (cylinderSource s l)
        ((factorizationData s).p.app f)).π :=
  ((lifting_iff s _).mp ((factorizationData s).hp f)).2 l

/-- The original same-cardinal K data constructs both lifting classes and the whole WFS. -/
theorem weakFactorizationSystem :
    IsWeakFactorizationSystem (generators s).rlp.llp (generators s).rlp := by
  let _ : HasFunctorialFactorization (generators s).rlp.llp (generators s).rlp :=
    ⟨⟨factorizationData s⟩⟩
  exact IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hi p hp)

open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams

/-- Original source variance is the actual current native weighted-end source function. -/
abbrev mapSource {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  (PointedCGWH.NativeMappingSourceFunctor.source E).map f.op

omit B in
/-- The entire source function remains the original full native source-functor map. -/
theorem mapSource_original_function (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (fun (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (f : X ⟶ Y) => mapSource f E) =
      fun (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (f : X ⟶ Y) =>
        (PointedCGWH.NativeMappingSourceFunctor.source E).map f.op :=
  rfl

private theorem toZero_fibration (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (toZero E) := by
  let _ : IsFibrant E := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant E
  exact (HomotopicalAlgebra.fibration_iff _).mp
    ((isFibrant_iff_of_isTerminal (toZero E) zeroDiagramIsTerminal).mp inferInstance)

/-- Every native projective cofibration gives a genuine full source-mapping fibration. -/
theorem mapSource_fibration
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) f)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    fibrations PointedCGWH.{u, v} (mapSource f E) := by
  let _ : IsFibrant E := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant E
  exact PointedCGWH.NativeCurrentBrownMapping.source_fibration f hf E

/-- The whole original trivial-cofibration class gives native source-mapping trivial fibrations. -/
theorem mapSource_trivialFibration
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) f)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    trivialFibrations PointedCGWH.{u, v} (mapSource f E) := by
  let _ : IsFibrant E := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant E
  exact PointedCGWH.NativeCurrentBrownMapping.source_trivial_fibration f hf E

/-- Brown's original factorization proves weak source invariance on actual cofibrant endpoints. -/
theorem mapSource_weak_of_cofibrant
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    [IsCofibrant X] [IsCofibrant Y] [WeakEquivalence f]
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    weakEquivalences PointedCGWH.{u, v} (mapSource f E) := by
  let _ : IsFibrant E := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant E
  have h := PointedCGWH.NativeCurrentBrownMapping.source_weak f E
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp h

/-- The same original native cylinder is cofibrant by its actual source cofibration. -/
theorem cylinder_cofibrant (l : L) : IsCofibrant (cylinder s l) := by
  let _ : IsCofibrant (CategoryTheory.Arrow.mk (stabilization s l)).left :=
    stabilization_source_cofibrant s l
  let _ : Cofibration (cylinderSource s l) := cylinderSource_cofibration s l
  exact isCofibrant_of_cofibration (cylinderSource s l)

/-- The original weak cylinder retraction acts weakly on every actual native mapping end. -/
theorem cylinderRetraction_source_weak (l : L)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    weakEquivalences PointedCGWH.{u, v} (mapSource (cylinderRetraction s l) E) := by
  let _ : IsCofibrant (cylinder s l) := cylinder_cofibrant s l
  let _ : IsCofibrant (CategoryTheory.Arrow.mk (stabilization s l)).right :=
    stabilization_target_cofibrant s l
  let _ : WeakEquivalence (cylinderRetraction s l) := cylinderRetraction_weak s l
  exact mapSource_weak_of_cofibrant (cylinderRetraction s l) E

omit B in
/-- Every whole native Arrow keeps the original reversed mapping-cylinder source composition. -/
theorem mapping_source_fac
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (PointedCGWH.NativeMappingSourceFunctor.source E).map
        (PointedCGWH.EnrichedIntervalMappingCylinder.retraction f).op ≫
      (PointedCGWH.NativeMappingSourceFunctor.source E).map
        (PointedCGWH.EnrichedIntervalMappingCylinder.source f).op =
      (PointedCGWH.NativeMappingSourceFunctor.source E).map f.hom.op :=
  originalCylinder_mapping_factorization f E

omit B in
private theorem originalCylinder_mapping_weak_iff
    (f : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (hr : weakEquivalences PointedCGWH.{u, v}
      ((PointedCGWH.NativeMappingSourceFunctor.source E).map
        (PointedCGWH.EnrichedIntervalMappingCylinder.retraction f).op)) :
    weakEquivalences PointedCGWH.{u, v}
        ((PointedCGWH.NativeMappingSourceFunctor.source E).map
          (PointedCGWH.EnrichedIntervalMappingCylinder.source f).op) ↔
      weakEquivalences PointedCGWH.{u, v}
        ((PointedCGWH.NativeMappingSourceFunctor.source E).map f.hom.op) :=
  originalWeakFactorization_iff (weakEquivalences PointedCGWH.{u, v})
    ((PointedCGWH.NativeMappingSourceFunctor.source E).map
      (PointedCGWH.EnrichedIntervalMappingCylinder.retraction f).op)
    ((PointedCGWH.NativeMappingSourceFunctor.source E).map
      (PointedCGWH.EnrichedIntervalMappingCylinder.source f).op)
    ((PointedCGWH.NativeMappingSourceFunctor.source E).map f.hom.op)
    (mapping_source_fac f E) hr

/-- The original factorization and actual weak retraction compare the full native source tests. -/
theorem cylinderSource_weak_iff (l : L)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    weakEquivalences PointedCGWH.{u, v} (mapSource (cylinderSource s l) E) ↔
      weakEquivalences PointedCGWH.{u, v} (mapSource (stabilization s l) E) :=
  originalCylinder_mapping_weak_iff (CategoryTheory.Arrow.mk (stabilization s l)) E
    (cylinderRetraction_source_weak s l E)

omit B in
/-- The literal native free source test detects the actual original operator Omega transpose. -/
theorem stabilization_mapping_weak_iff (l : L)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    weakEquivalences PointedCGWH.{u, v} (mapSource (stabilization s l) E) ↔
      weakEquivalences PointedCGWH.{u, v} (adjoint s l E) :=
  CurrentFree.stabilizationMapping_property_iff (weakEquivalences PointedCGWH.{u, v})
    (s.source l) (s.target l) (s.coefficient l) (s.inclusion l) E

/-- The original zero-target K corner detects exactly the native source-defined Omega map. -/
theorem zeroCorner_trivialFibration_iff (l : L)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    trivialFibrations PointedCGWH.{u, v}
      (PointedCGWH.NativeMappingCorner.square (cylinderSource s l) (toZero E)).π ↔
      weakEquivalences PointedCGWH.{u, v} (adjoint s l E) := by
  rw [(trivialFibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (PointedCGWH.NativeMappingZeroSource.cornerArrowIso (cylinderSource s l) E)]
  change (fibrations PointedCGWH.{u, v} (mapSource (cylinderSource s l) E) ∧
    weakEquivalences PointedCGWH.{u, v} (mapSource (cylinderSource s l) E)) ↔ _
  have hF := mapSource_fibration (cylinderSource s l)
    ((HomotopicalAlgebra.cofibration_iff _).mp (cylinderSource_cofibration s l)) E
  rw [and_iff_right hF, cylinderSource_weak_iff, stabilization_mapping_weak_iff]

/-- Full original K lifting recognizes level-fibrant native Omega objects in both directions. -/
theorem lifting_toZero_iff_fibrantOmega (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (generators s).rlp (toZero E) ↔ IsFibrant E ∧ IsOmega s E := by
  constructor
  · intro h
    have hp := (lifting_iff s (toZero E)).mp h
    refine ⟨(isFibrant_iff_of_isTerminal (toZero E) zeroDiagramIsTerminal).mpr
      ((HomotopicalAlgebra.fibration_iff _).mpr hp.1), fun l => ?_⟩
    exact (zeroCorner_trivialFibration_iff s l E).mp (hp.2 l)
  · rintro ⟨hF, hOmega⟩
    apply (lifting_iff s (toZero E)).mpr
    refine ⟨(HomotopicalAlgebra.fibration_iff _).mp
      ((isFibrant_iff_of_isTerminal (toZero E) zeroDiagramIsTerminal).mp hF), fun l => ?_⟩
    exact (zeroCorner_trivialFibration_iff s l E).mpr (hOmega l)

/-- The native level model makes original K-locality the original Omega condition. -/
theorem lifting_toZero_iff_isOmega (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (generators s).rlp (toZero E) ↔ IsOmega s E := by
  rw [lifting_toZero_iff_fibrantOmega, and_iff_right
    (HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant E)]

/-- Every actual caller-chosen zero fiber of a K-right map has its original
K-right collapse, terminal K-locality, and Omega condition on the same cone point. -/
theorem chosenFiber_right_local_omega
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y)
    (hp : (generators s).rlp p)
    (c : PullbackCone p (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroTo Y))
    (hc : IsLimit c) :
    (generators s).rlp c.snd ∧
      (generators s).rlp (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero c.pt) ∧
        IsOmega s c.pt := by
  have hCollapse : (generators s).rlp c.snd :=
    MorphismProperty.of_isPullback (IsPullback.of_isLimit hc) hp
  have hTerminal : (generators s).rlp
      (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero c.pt) := by
    have hEq : c.snd = HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero c.pt :=
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagramIsTerminal.hom_ext _ _
    rwa [hEq] at hCollapse
  exact ⟨hCollapse, hTerminal, (lifting_toZero_iff_isOmega s c.pt).mp hTerminal⟩

/-- Every actual Omega target makes its original cylinder source map a native trivial fibration. -/
theorem cylinderSource_mapping_trivialFibration (l : L)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) (hE : IsOmega s E) :
    trivialFibrations PointedCGWH.{u, v} (mapSource (cylinderSource s l) E) := by
  have h := (zeroCorner_trivialFibration_iff s l E).mpr (hE l)
  exact ((trivialFibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (PointedCGWH.NativeMappingZeroSource.cornerArrowIso (cylinderSource s l) E)).mp h

/-- The actual original terminal Arrow family retains each given source object and map. -/
def zeroArrows : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤
    CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  toZeroArrow

omit B in
/-- The retained zero-arrow name is the whole canonical original terminal-arrow functor. -/
theorem zeroArrows_eq_toZeroArrow :
    (zeroArrows (I := I) : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤
      CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) = toZeroArrow := rfl

/-- The original K middle functor applied to the actual original zero-arrow family. -/
def omegaReplacement : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} I :=
  toZeroArrow ⋙ (factorizationData s).Z

/-- The actual K injection gives the whole original native Omega replacement unit. -/
def omegaReplacementUnit : 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶ omegaReplacement s where
  app X := (factorizationData s).i.app (CategoryTheory.Arrow.mk (toZero X))
  naturality _ _ f := (factorizationData s).i.naturality (toZeroArrow.map f)

/-- Every replacement map is the full original K map of the same original source square. -/
theorem omegaReplacement_map {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    (omegaReplacement s).map f = SmallObject.objMap (generators s) realizedGeneratorCardinal.{v}
      (CategoryTheory.Arrow.homMk f (𝟙 zeroDiagram) (zeroDiagramIsTerminal.hom_ext _ _)) := rfl

/-- The entire original replacement projection is the original K right factor. -/
abbrev omegaReplacementProjection (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  (factorizationData s).p.app (CategoryTheory.Arrow.mk (toZero X))

/-- Every original unit is K-left without a source cofibrancy premise. -/
theorem omegaReplacementUnit_mem_left (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (generators s).rlp.llp ((omegaReplacementUnit s).app X) :=
  (factorizationData s).hi (CategoryTheory.Arrow.mk (toZero X))

/-- The actual original unit is a native projective cofibration on every source. -/
theorem omegaReplacementUnit_cofibration (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) ((omegaReplacementUnit s).app X) :=
  left_le_cofibrations s _ (omegaReplacementUnit_mem_left s X)

/-- The original projection has the full K-right condition at every original source object. -/
theorem omegaReplacementProjection_mem_right (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (generators s).rlp (omegaReplacementProjection s X) :=
  (factorizationData s).hp (CategoryTheory.Arrow.mk (toZero X))

/-- The original projection is literally the selected terminal map of the actual middle object. -/
theorem omegaReplacementProjection_eq_toZero (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    omegaReplacementProjection s X = toZero ((omegaReplacement s).obj X) :=
  zeroDiagramIsTerminal.hom_ext _ _

/-- The original K/cardinal algorithm constructs actual native Omega objects on every input. -/
theorem omegaReplacement_isOmega (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    IsOmega s ((omegaReplacement s).obj X) := by
  apply (lifting_toZero_iff_isOmega s _).mp
  rw [← omegaReplacementProjection_eq_toZero]
  exact omegaReplacementProjection_mem_right s X

/-- The actual original replacement preserves cofibrant sources by its actual original injection. -/
theorem omegaReplacement_isCofibrant (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    [IsCofibrant X] : IsCofibrant ((omegaReplacement s).obj X) := by
  let i : X ⟶ (omegaReplacement s).obj X := (omegaReplacementUnit s).app X
  let _ : Cofibration i :=
    (HomotopicalAlgebra.cofibration_iff _).mpr (omegaReplacementUnit_cofibration s X)
  exact isCofibrant_of_cofibration i

/-- Every whole original native input retains the same original unit square. -/
theorem omegaReplacementUnit_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    f ≫ (omegaReplacementUnit s).app Y =
      (omegaReplacementUnit s).app X ≫ (omegaReplacement s).map f :=
  (omegaReplacementUnit s).naturality f

/-- The weak-test candidate uses the actual level homotopy functor and original Omega targets. -/
def omegaTests : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  fun _X Y f => ∀ E : EnrichedFunctorCat PointedCGWH.{u, v} I, IsOmega s E →
    Function.Bijective
      (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y ⟶
          (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj E =>
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ g)

/-- The original Omega tests are exactly the Hom tests against the original K-right zero arrows. -/
theorem omegaTests_eq_lifting_tests : omegaTests s =
    fun _X Y f => ∀ E : EnrichedFunctorCat PointedCGWH.{u, v} I,
      (generators s).rlp (toZero E) → Function.Bijective
        (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y ⟶
            (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj E =>
          (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ g) := by
  ext X Y f
  constructor
  · intro h E hE
    exact h E ((lifting_toZero_iff_isOmega s E).mp hE)
  · intro h E hE
    exact h E ((lifting_toZero_iff_isOmega s E).mpr hE)

/-- The canonical whole Omega class is the intersection of its actual targetwise Hom tests. -/
theorem omegaTests_eq_iInf_isomorphisms :
    omegaTests s =
      ⨅ E : {E : EnrichedFunctorCat PointedCGWH.{u, v} I // IsOmega s E},
        ((MorphismProperty.isomorphisms (Type (v + 1))).inverseImage
          ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).op ⋙
            yoneda.obj
              ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj E.1))).unop := by
  ext X Y f
  rw [MorphismProperty.iInf_iff]
  constructor
  · intro h E
    exact (CategoryTheory.isIso_iff_bijective _).2 (h E.1 E.2)
  · intro h E hE
    exact (CategoryTheory.isIso_iff_bijective _).1 (h ⟨E, hE⟩)

/-- Identity arrows satisfy the canonical original Omega tests. -/
instance omegaTests.containsIdentities : (omegaTests s).ContainsIdentities := by
  rw [omegaTests_eq_iInf_isomorphisms s]
  infer_instance

/-- Composition and both cancellation directions hold for the same canonical Omega class. -/
instance omegaTests.hasTwoOutOfThreeProperty :
    (omegaTests s).HasTwoOutOfThreeProperty := by
  rw [omegaTests_eq_iInf_isomorphisms s]
  refine { toIsStableUnderComposition := inferInstance
           of_postcomp := ?_
           of_precomp := ?_ }
  · intro X Y Z f g hg hfg
    rw [MorphismProperty.iInf_iff] at hg hfg ⊢
    intro E
    exact (((MorphismProperty.isomorphisms (Type (v + 1))).inverseImage
      ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).op ⋙
        yoneda.obj
          ((toHomotopyCategory
            (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj E.1))).unop).of_postcomp
      f g (hg E) (hfg E)
  · intro X Y Z f g hf hfg
    rw [MorphismProperty.iInf_iff] at hf hfg ⊢
    intro E
    exact (((MorphismProperty.isomorphisms (Type (v + 1))).inverseImage
      ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).op ⋙
        yoneda.obj
          ((toHomotopyCategory
            (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj E.1))).unop).of_precomp
      f g (hf E) (hfg E)

/-- Whole Arrow retracts preserve the canonical original Omega tests. -/
instance omegaTests.isStableUnderRetracts : (omegaTests s).IsStableUnderRetracts where
  of_retract h hg := by
    rw [omegaTests_eq_iInf_isomorphisms s] at hg ⊢
    rw [MorphismProperty.iInf_iff] at hg ⊢
    intro E
    exact MorphismProperty.of_retract h (hg E)

/-- Every actual original level weak map satisfies all native Omega tests. -/
theorem levelWeak_le_omegaTests : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ≤
    omegaTests s := by
  intro X Y f hf E _
  have hInv : IsIso ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map f).mp hf
  exact (isIso_iff_coyoneda_map_bijective _).mp hInv
    ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj E)

/-- On native Omega objects, the original tests detect the level weak class. -/
theorem omegaTests_iff_levelWeak_of_isOmega
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hX : IsOmega s X) (hY : IsOmega s Y) :
    omegaTests s f ↔ weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f := by
  constructor
  · intro hf
    let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
    obtain ⟨g, hfg⟩ := (hf X hX).2 (𝟙 (H.obj X))
    have hfg' : H.map f ≫ g = 𝟙 (H.obj X) := hfg
    have hgf : g ≫ H.map f = 𝟙 (H.obj Y) := by
      apply (hf Y hY).1
      change H.map f ≫ (g ≫ H.map f) = H.map f ≫ 𝟙 (H.obj Y)
      rw [← Category.assoc, hfg', Category.id_comp, Category.comp_id]
    have hInv : IsIso (H.map f) := ⟨g, hfg, hgf⟩
    exact (weakEquivalence_iff_isIso_toHomotopyCategory_map f).mpr hInv
  · exact levelWeak_le_omegaTests s f

end NativeK

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
