/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.ScalarCotensorInterchange
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarCompatibility
public import
MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKAllSourceLocality

/-!
# Entire original K classes under scalar tensor and cotensor

The native scalar/mapping interchange transports every original cylinder mapping
corner. Actual base SM7 and full K lifting then prove cotensor closure of K-right
and scalar pushout closure of the entire K-left class. Genuine all-index Hom
cofibrancy supplies the original all-source Omega tests.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- Every given scalar cotensor square sends the entire original K-right class into itself. -/
theorem pullbackCotensor_right {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y)
    (hj : cofibrations PointedCGWH.{u, v} j) (hp : (generators s).rlp p)
    (sq : (ScalarLeibniz.cotensorBifunctor (V := PointedCGWH.{u, v}) (A := I)).PullbackObjObj
      j p) : (generators s).rlp sq.π := by
  have h := (lifting_iff (B := B) s p).mp hp
  refine (lifting_iff (B := B) s sq.π).mpr ⟨?_, fun l => ?_⟩
  · exact ScalarCompatibility.pullbackCotensor_fibration (B := B) j p hj h.1 sq
  · let inner := PointedCGWH.NativeMappingCorner.square (cylinderSource s l) p
    let left := PointedCGWH.NativeMappingCorner.square (cylinderSource s l) sq.π
    let right := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom j inner.π
    have hRight : trivialFibrations PointedCGWH.{u, v} right.π :=
      PointedCGWH.CurrentCanonicalSmashSM7.trivial_right j inner.π hj (h.2 l) right
    let iso := PointedCGWH.EnrichedScalarCotensorInterchange.givenSquareInterchangeIso
      j (cylinderSource s l) p sq left inner right
    exact ((trivialFibrations PointedCGWH.{u, v}).arrow_mk_iso_iff iso).mpr hRight

/-- Every given scalar pushout square preserves the entire original K-left class. -/
theorem scalarPushout_left {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hj : cofibrations PointedCGWH.{u, v} j) (hf : (generators s).rlp.llp f)
    (sq : (ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)).PushoutObjObj
      j f) : (generators s).rlp.llp sq.ι := by
  intro A C p hp
  let pb := ScalarLeibniz.pullbackSquare j p
  have hpb : (generators s).rlp pb.π :=
    pullbackCotensor_right (B := B) s j p hj hp pb
  exact ((ScalarLeibniz.parametrizedAdjunction (V := PointedCGWH.{u, v}) (A :=
      I)).hasLiftingProperty_iff sq pb).mpr (hf pb.π hpb)

/-- The same original scalar pushout is a cofibration in the actual native level model. -/
theorem scalarPushout_cofibration {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hj : cofibrations PointedCGWH.{u, v} j) (hf : (generators s).rlp.llp f)
    (sq : (ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)).PushoutObjObj
      j f) : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) sq.ι :=
  (left_le_cofibrations (B := B) s) _ (scalarPushout_left (B := B) s j f hj hf sq)

/-- Genuine all-index Hom cofibrancy gives every original local test for this same pushout. -/
theorem scalarPushout_localTests
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hj : cofibrations PointedCGWH.{u, v} j) (hf : (generators s).rlp.llp f)
    (sq : (ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)).PushoutObjObj
      j f) : localTestEquivalences s sq.ι :=
  originalKLeft_localTests (B := B) s hHom sq.ι (scalarPushout_left (B := B) s j f hj hf sq)

/-- The full K-left closure, native cofibration, and all-source local tests hold together. -/
theorem scalarPushout_left_cofibration_localTests
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hj : cofibrations PointedCGWH.{u, v} j) (hf : (generators s).rlp.llp f)
    (sq : (ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)).PushoutObjObj j f) :
    (generators s).rlp.llp sq.ι ∧
      cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) sq.ι ∧
        localTestEquivalences s sq.ι :=
  ⟨scalarPushout_left (B := B) s j f hj hf sq,
    scalarPushout_cofibration (B := B) s j f hj hf sq,
    scalarPushout_localTests (B := B) s hHom j f hj hf sq⟩

/-- The same scalar pushout induces every original Omega-target precomposition bijection. -/
theorem scalarPushout_omegaTests_allSource
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {M N : PointedCGWH.{u, v}} (j : M ⟶ N)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hj : cofibrations PointedCGWH.{u, v} j) (hf : (generators s).rlp.llp f)
    (sq : (ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)).PushoutObjObj j f)
    (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) (hZ : IsOmega s Z) :
    Function.Bijective
      (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
          (tensorLeftObject N Y) ⟶
          (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map sq.ι ≫ g) :=
  ((originalLocalTestEquivalence_iff_omegaTests (B := B) s) sq.ι).mp
    (scalarPushout_localTests (B := B) s hHom j f hj hf sq) Z hZ

omit B in
/-- The native scalar functor preserves initial objects in its coefficient variable. -/
private instance scalarPreservesInitial (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PreservesColimitsOfShape (Discrete PEmpty.{1})
      ((ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)).flip.obj X) := by
  let _ : PreservesColimits
      ((ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)).flip.obj X) :=
    (PointedCGWH.EnrichedFunctorMapping.tensorMappingAdjunction X).leftAdjoint_preservesColimits
  infer_instance

/-- A cofibrant scalar preserves the complete original K-left class. -/
theorem tensorMap_left (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : (generators s).rlp.llp f) :
    (generators s).rlp.llp ((EnrichedFunctorCat.tensorLeft M).map f) := by
  let sq := Functor.PushoutObjObj.ofIsInitialLeft
    (ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I))
      (initial.to M) f initialIsInitial
  exact scalarPushout_left (B := B) s (initial.to M) f
    ((cofibration_iff _).mp inferInstance) hf sq

/-- The original scalar adjunction transfers K lifting to its actual cotensor map. -/
theorem cotensorMap_right (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y)
    (hp : (generators s).rlp p) :
    (generators s).rlp ((cotensor M).map p) := by
  intro A C i hi
  have hLi : (generators s).rlp.llp ((EnrichedFunctorCat.tensorLeft M).map i) :=
    tensorMap_left (B := B) s M i ((generators s).le_llp_rlp i hi)
  exact ((ScalarLeibniz.adjunction M).hasLiftingProperty_iff i p).mp (hLi p hp)

omit B in
/-- Cotensoring the unchanged zero diagram gives a zero diagram on the same index. -/
theorem cotensorZero_isZero (M : PointedCGWH.{u, v}) :
    IsZero ((cotensor M (I := I)).obj Diagrams.zeroDiagram) := by
  apply EnrichedZeroCompletion.diagram_isZero_of_obj_isZero
  intro a
  exact EnrichedZeroCompletion.ihom_isZero_target M (Diagrams.initialDiagram_component_isZero a)

/-- Cofibrant scalar cotensoring preserves the full original Omega condition. -/
theorem cotensor_isOmega (M : PointedCGWH.{u, v}) [IsCofibrant M]
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) (hE : IsOmega s E) :
    IsOmega s ((cotensor M).obj E) := by
  have hp := cotensorMap_right (B := B) s M (Diagrams.toZero E)
    ((lifting_toZero_iff_isOmega (B := B) s E).mpr hE)
  let e : (cotensor M (I := I)).obj Diagrams.zeroDiagram ≅ Diagrams.zeroDiagram :=
    (cotensorZero_isZero M).iso Diagrams.zeroDiagram_isZero
  have hEq : (cotensor M).map (Diagrams.toZero E) ≫ e.hom =
      Diagrams.toZero ((cotensor M).obj E) := Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  apply (lifting_toZero_iff_isOmega (B := B) s _).mp
  rw [← hEq]
  exact (generators s).rlp.comp_mem _ _ hp ((generators s).rlp_of_isIso e.hom)

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
