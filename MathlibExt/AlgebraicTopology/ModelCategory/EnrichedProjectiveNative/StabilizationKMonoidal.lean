/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKScalarTestPreservation
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.DerivedLocalMapping
public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingPushout
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClassComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedMonoCofibration

/-!
# Quillen adjunctions and the original native stabilization tests

A level Quillen adjunction whose actual right adjoint preserves the original
Ω condition preserves the original Ω-target tests on cofibrant source objects.
The complete forward and inverse ordinary homotopy-category Hom functions
come from the given adjunction. The arbitrary-source statement applies the
original native I replacement to the whole caller arrow.

This is a sufficient criterion. Its right-adjoint locality hypothesis must be
proved from the actual native smash and internal Hom before it can establish
stable monoidality; no stable model structure is selected here.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed Simplicial

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

section AdjointTests

variable {F G : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤
  EnrichedFunctorCat PointedCGWH.{u, v} I}
  (adj : F ⊣ G) [adj.IsQuillenAdjunction]

include adj

/-- The actual right-adjoint Ω closure transfers every original test through
both complete Hom functions, for arbitrary cofibrant original endpoints. -/
theorem adjointMap_omegaTests_of_cofibrant
    (hG : ∀ E : EnrichedFunctorCat PointedCGWH.{u, v} I,
      IsOmega s E → IsOmega s (G.obj E))
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) (hf : omegaTests s f) :
    omegaTests s (F.map f) := by
  intro E hE
  let _ : IsFibrant E := Native.allObjectsFibrant E
  let eX := QuillenOrdinaryHoHom.homEquiv adj X E
  let eY := QuillenOrdinaryHoHom.homEquiv adj Y E
  have h := hf (G.obj E) (hG E hE)
  constructor
  · intro g₁ g₂ hg
    apply eY.injective
    apply h.1
    have h₁ := QuillenOrdinaryHoHom.homEquiv_naturality_left adj E f g₁
    have h₂ := QuillenOrdinaryHoHom.homEquiv_naturality_left adj E f g₂
    exact h₁.symm.trans ((congrArg eX hg).trans h₂)
  · intro g
    obtain ⟨a, ha⟩ := h.2 (eX g)
    refine ⟨eY.symm a, ?_⟩
    apply eX.injective
    change QuillenOrdinaryHoHom.homEquiv adj X E
      ((toHomotopyCategory _).map (F.map f) ≫ eY.symm a) = _
    rw [QuillenOrdinaryHoHom.homEquiv_naturality_left]
    change (toHomotopyCategory _).map f ≫ eY (eY.symm a) = _
    rw [Equiv.apply_symm_apply]
    exact ha

/-- The same adjunction acts on the whole original I-replacement arrow,
including both replacement endpoints and its unchanged map. -/
theorem adjointQMap_omegaTests
    (hG : ∀ E : EnrichedFunctorCat PointedCGWH.{u, v} I,
      IsOmega s E → IsOmega s (G.obj E))
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : omegaTests s f) :
    omegaTests s (F.map ((Replacement.cofibrantReplacement (B := B)).map f)) := by
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) X
  let _ := Replacement.isCofibrant_cofibrantReplacement (B := B) Y
  exact adjointMap_omegaTests_of_cofibrant s adj hG
    ((Replacement.cofibrantReplacement (B := B)).map f)
    ((cofibrantReplacement_map_localTest_iff s f).mpr hf)

end AdjointTests

/-- A cofibration that is an original Ω-test equivalence stays one under
the caller's actual chosen pushout, with all original endpoints retained.
Its mapping map is the pullback of the original trivial mapping fibration.
The new endpoint is proved cofibrant from the same pushout leg. -/
theorem pushout_cofibration_omegaTests
    {A B Z C : EnrichedFunctorCat PointedCGWH.{u, v} I}
    [IsCofibrant A] [IsCofibrant B] [IsCofibrant Z]
    (i : A ⟶ B) (z : A ⟶ Z) (kB : B ⟶ C) (kZ : Z ⟶ C)
    (sq : IsPushout i z kB kZ)
    (hi : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) i)
    (hTests : omegaTests s i) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) kZ ∧ omegaTests s kZ := by
  have hkZ : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) kZ :=
    CategoryTheory.MorphismProperty.of_isPushout sq.flip hi
  let _ : Cofibration kZ := (cofibration_iff kZ).mpr hkZ
  let _ : IsCofibrant C := isCofibrant_of_cofibration kZ
  refine ⟨hkZ, ?_⟩
  apply DerivedLocalMapping.omegaTests_of_mappingPre_weak s kZ
  intro E hE
  have hMap : trivialFibrations PointedCGWH.{u, v} (WeightedEndVariance.pre i E) :=
    ⟨mapSource_fibration i hi E,
      DerivedLocalMapping.mappingPre_weak_of_omegaTests s i hTests E hE⟩
  have hPullback := PointedCGWH.NativeMappingPushout.sourceSquare i z kB kZ sq E
  have hLeg : trivialFibrations PointedCGWH.{u, v} (WeightedEndVariance.pre kZ E) :=
    CategoryTheory.MorphismProperty.of_isPullback hPullback hMap
  exact hLeg.2

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK


namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

private theorem realizedMap_cofibration {X Y : SSet.{v}} (f : X ⟶ Y) [Mono f] :
    cofibrations CGWH.{u, v} (SSet.toCGWH.{u, v}.map f) := by
  change CGWH.modelCofibrations.{u, v} (SSet.toCGWH.map f)
  rw [CGWH.modelCofibrations_eq_inverseImage]
  change TopCat.realizedBoundaryInclusions.{v}.rlp.llp (SSet.toTop.map f)
  exact SSet.toTop_map_mem_realizedBoundaryLLP f

private theorem realizedObject_cofibrant (X : SSet.{v}) :
    IsCofibrant (SSet.toCGWH.{u, v}.obj X) := by
  let _ : SSet.toCGWH.{u, v}.IsLeftAdjoint := SSet.sSetCGWHAdj.isLeftAdjoint
  let _ : Cofibration (SSet.toCGWH.{u, v}.map (initial.to X)) :=
    (cofibration_iff _).mpr (realizedMap_cofibration (initial.to X))
  have hInitial : IsInitial (SSet.toCGWH.{u, v}.obj (⊥_ SSet.{v})) :=
    initialIsInitial.isInitialObj (G := SSet.toCGWH.{u, v})
  exact (isCofibrant_iff_of_isInitial (SSet.toCGWH.map (initial.to X)) hInitial).mpr
    inferInstance

private theorem finitePointedRealization_cofibrant (X : SSet.{v}) [X.Finite] :
    IsCofibrant ((Under.costar CGWH.point.{u, v}).obj (SSet.toCGWHOfFinite X)) := by
  let _ : IsCofibrant (SSet.toCGWH.{u, v}.obj X) := realizedObject_cofibrant X
  let e := CGWH.finiteRealizationIso.{u, v} X
  let _ : IsCofibrant (SSet.toCGWHOfFinite X : CGWH.{u, v}) :=
    isCofibrant_of_cofibration e.hom
  let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := Under.costarAdjForget CGWH.point.{u, v}) inferInstance


open MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private theorem freeFamily_endpoints (P : MorphismProperty PointedCGWH.{u, v})
    (hP : ∀ {A C : PointedCGWH.{u, v}} (i : A ⟶ C), P i → IsCofibrant A ∧ IsCofibrant C)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : HomotopicalAlgebra.EnrichedProjective.generators P f) :
    IsCofibrant X ∧ IsCofibrant Y := by
  obtain ⟨q, hq⟩ := (MorphismProperty.adjointFamilyGenerators_iff
    (fun a : I => Free.functor (V := PointedCGWH.{u, v}) a) P f).mp hf
  have he := hP q.2.1.hom q.2.2
  let _ : IsCofibrant q.2.1.left := he.1
  let _ : IsCofibrant q.2.1.right := he.2
  have hX := congrArg (fun g => g.left) hq
  have hY := congrArg (fun g => g.right) hq
  change X = (Free.functor q.1).obj q.2.1.left at hX
  change Y = (Free.functor q.1).obj q.2.1.right at hY
  rw [hX, hY]
  exact ⟨freeAt_obj_isCofibrant q.1 q.2.1.left,
    freeAt_obj_isCofibrant q.1 q.2.1.right⟩

omit B in
theorem pointedBoundary_endpoints {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : PointedCGWH.realizedBoundaryInclusions f) : IsCofibrant X ∧ IsCofibrant Y := by
  change (CGWH.realizedBoundaryInclusions.strictMap (Under.costar CGWH.point)) f at hf
  cases hf with
  | map h =>
    obtain ⟨m⟩ := h
    exact ⟨finitePointedRealization_cofibrant (SSet.boundary m),
      finitePointedRealization_cofibrant (Δ[m] : SSet.{v})⟩

omit B in
theorem pointedHorn_endpoints {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : PointedCGWH.realizedHornInclusions f) : IsCofibrant X ∧ IsCofibrant Y := by
  change (CGWH.realizedHornInclusions.strictMap (Under.costar CGWH.point)) f at hf
  cases hf with
  | map h =>
    rw [CGWH.realizedHornInclusions, MorphismProperty.iSup_iff] at h
    obtain ⟨m, ⟨k⟩⟩ := h
    exact ⟨finitePointedRealization_cofibrant (Λ[m + 1, k] : SSet.{v}),
      finitePointedRealization_cofibrant (Δ[m + 1] : SSet.{v})⟩

/-- Every original free realized-boundary generator has its actual cofibrant endpoints. -/
theorem levelI_generatorEndpoints {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : NativeK.levelI f) : IsCofibrant X ∧ IsCofibrant Y :=
  freeFamily_endpoints PointedCGWH.realizedBoundaryInclusions pointedBoundary_endpoints f hf

/-- Every original free realized-horn generator has its actual cofibrant endpoints. -/
theorem levelJ_generatorEndpoints {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : NativeK.levelJ f) : IsCofibrant X ∧ IsCofibrant Y :=
  freeFamily_endpoints PointedCGWH.realizedHornInclusions pointedHorn_endpoints f hf

/-- Both endpoints of every original paired boundary/mapping-cylinder K generator are cofibrant. -/
theorem additionalGeneratorEndpoints (s : NativeStabilizationFamily.{u, v} I L) (l : L) (m : ℕ) :
    IsCofibrant (Arrow.mk (NativeK.generatorMap s l m)).left ∧
      IsCofibrant (Arrow.mk (NativeK.generatorMap s l m)).right := by
  let A := (Arrow.mk (NativeK.boundaryMap.{u, v} m)).left
  let C := (Arrow.mk (NativeK.boundaryMap.{u, v} m)).right
  let X := (Arrow.mk (NativeK.stabilization s l)).left
  let Y := NativeK.cylinder s l
  let _ : IsCofibrant A := finitePointedRealization_cofibrant (SSet.boundary m)
  let _ : IsCofibrant C := finitePointedRealization_cofibrant (Δ[m] : SSet.{v})
  let _ : IsCofibrant X := NativeK.stabilization_source_cofibrant s l
  let _ : IsCofibrant Y := NativeK.cylinder_cofibrant s l
  let _ : (ScalarLeibniz.adjunction (A := I) A).IsQuillenAdjunction :=
    ScalarCompatibility.scalar_isQuillen A
  let _ : (ScalarLeibniz.adjunction (A := I) C).IsQuillenAdjunction :=
    ScalarCompatibility.scalar_isQuillen C
  let po := NativeK.generatorSquare s l m
  have hg : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((ScalarLeibniz.tensorBifunctor.obj A).map (NativeK.cylinderSource s l)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrations
      (adj := ScalarLeibniz.adjunction A) _
      ((cofibration_iff _).mp (NativeK.cylinderSource_cofibration s l))
  have hInl : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) po.inl :=
    MorphismProperty.of_isPushout po.isPushout hg
  let _ : Cofibration po.inl := (cofibration_iff _).mpr hInl
  have hBase : IsCofibrant (Arrow.mk po.inl).left := by
    change IsCofibrant ((WeightedEndVariance.tensorBifunctor.obj C).obj X)
    rw [← ScalarTensorFunctorValue.scalar_weighted_tensor]
    exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := ScalarLeibniz.adjunction C) inferInstance
  let _ : IsCofibrant (Arrow.mk po.inl).left := hBase
  have hP : IsCofibrant po.pt := isCofibrant_of_cofibration (hX := hBase) po.inl
  have hTarget : IsCofibrant ((WeightedEndVariance.tensorBifunctor.obj C).obj Y) := by
    rw [← ScalarTensorFunctorValue.scalar_weighted_tensor]
    exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := ScalarLeibniz.adjunction C) inferInstance
  exact ⟨hP, hTarget⟩



/-- The complete original K union has cofibrant endpoints, with every horn
and every original correlated boundary/cylinder generator retained. -/
theorem generatorEndpoints (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : generators s f) : IsCofibrant X ∧ IsCofibrant Y := by
  rcases (generators_iff s f).mp hf with hJ | hExtra
  · exact levelJ_generatorEndpoints f hJ
  · obtain ⟨⟨l, m⟩⟩ := hExtra
    exact additionalGeneratorEndpoints s l m

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
