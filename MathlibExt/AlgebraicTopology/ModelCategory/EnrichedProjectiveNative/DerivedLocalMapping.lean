/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.SingularMappingModelCompatibility
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK
public import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Local
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKScalarClosure
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom
public import MathlibExt.Topology.Category.PointedCGWH.NativeOriginalParametrizedMapping
public import MathlibExt.CategoryTheory.Enriched.ScalarCotensorUnit

/-!
# Derived local objects for the original native stabilization family

The localizing Arrow family is the whole original native stabilization
family, including each complete source, target, coefficient and inclusion.
Native weak equivalences of the actual singular mapping ends and the
framework's chosen strict-to-derived comparison identify derived-local
fibrant objects with the original full-family Omega condition.

The actual parametrized tensor/mapping and scalar/cotensor Quillen pairs
give ordinary homotopy-category Hom equivalences. Closure of Omega
objects under every cofibrant scalar cotensor then detects weakness of
the complete original mapping map. The actual cofibrant counit and
fibrant unit extend this calculation to arbitrary arrows, proving that
derived local equivalences are exactly the original Omega Hom tests.
The native stable model construction remains a separate required join.

The level model and simplicial enrichment are constructed from the existing
native providers. No model or derived-local detection result is supplied
as an additional native hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.EnrichedFunctorCat MonoidalCategory HomotopicalAlgebra
open PointedCGWH.SingularHomotopyGeometry
open scoped CGWH.modelCategory MonoidalClosed

attribute [local instance]
  HomotopicalAlgebra.EnrichedProjective.Native.SingularMapping.cofibrantFactorization
  HomotopicalAlgebra.EnrichedProjective.Native.SingularMapping.fibrantFactorization

namespace HomotopicalAlgebra.EnrichedProjective.Native.DerivedLocalMapping

open OperatorStabilizationK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

/-- The complete original native stabilization Arrow function on every actual family label. -/
def stabilizationArrows (l : L) :
    CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  CategoryTheory.Arrow.mk (NativeK.stabilization s l)

/-- Derived mapping against each original stabilization detects its actual adjoint structure map. -/
theorem stabilization_derivedWeak_iff (l : L)
    (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    SSet.realizationWeakEquivalences
        (derivedMappingPrecomp (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
          (stabilizationArrows s l).hom Z) ↔
      weakEquivalences PointedCGWH.{u, v} (NativeK.adjoint s l Z) := by
  let : IsCofibrant (EnrichedFunctorCat.Free.object (s.target l) (s.coefficient l)) :=
    NativeK.stabilization_source_cofibrant s l
  let : IsCofibrant (EnrichedFunctorCat.Free.object (s.source l) (𝟙_ PointedCGWH.{u, v})) :=
    NativeK.stabilization_target_cofibrant s l
  calc
    _ ↔ SSet.realizationWeakEquivalences
        (((SimplicialCategory.sHomFunctor (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          (NativeK.stabilization s l).op).app Z) :=
      SingularMapping.derivedPrecomp_weak_iff_strict (NativeK.stabilization s l) Z
    _ ↔ weakEquivalences PointedCGWH.{u, v}
        (NativeK.mapSource (NativeK.stabilization s l) Z) := by
      rw [SimplicialEnrichment.source_map]
      exact SingularMapping.singularFunctor_weak_iff _
    _ ↔ _ := NativeK.stabilization_mapping_weak_iff s l Z

/-- The original full native Omega condition is exactly derived locality for those same Arrows. -/
theorem isDerivedLocal_iff_isOmega (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    isDerivedLocal (stabilizationArrows s) Z ↔ NativeK.IsOmega s Z := by
  constructor
  · intro h l
    exact (stabilization_derivedWeak_iff s l Z).mp (h l)
  · intro h l
    exact (stabilization_derivedWeak_iff s l Z).mpr (h l)

/-- Every original native level object is fibrant, so local fibrancy is
precisely its Omega action. -/
theorem isLocalFibrant_iff_isOmega (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    isLocalFibrant (stabilizationArrows s) Z ↔ NativeK.IsOmega s Z :=
  ⟨fun h => (isDerivedLocal_iff_isOmega s Z).mp h.2,
    fun h => ⟨Native.allObjectsFibrant Z, (isDerivedLocal_iff_isOmega s Z).mpr h⟩⟩

end HomotopicalAlgebra.EnrichedProjective.Native.DerivedLocalMapping

namespace HomotopicalAlgebra.EnrichedProjective.Native.DerivedLocalMapping

universe uP vP uD vD
open CategoryTheory.Limits PointedCGWH.EnrichedFunctorMapping


private theorem inverseMappingHo_parameter
    {P : Type uP} [Category.{vP} P] [ModelCategory P]
    {D : Type uD} [Category.{vD} D] [ModelCategory D]
    {F : D ⥤ P ⥤ D} {G : Dᵒᵖ ⥤ D ⥤ P} (adj : F ⊣₂ G)
    {X Y : D} (f : X ⟶ Y) (M : P) [IsCofibrant M] (E : D) [IsFibrant E]
    [Adjunction.IsQuillenAdjunction (adj.adj X)]
    [Adjunction.IsQuillenAdjunction (adj.adj Y)]
    (g : (toHomotopyCategory P).obj M ⟶
      (toHomotopyCategory P).obj ((G.obj (Opposite.op Y)).obj E)) :
    (QuillenOrdinaryHoHom.homEquiv (adj.adj X) M E).symm
        (g ≫ (toHomotopyCategory P).map ((G.map f.op).app E)) =
      (toHomotopyCategory D).map ((F.map f).app M) ≫
        (QuillenOrdinaryHoHom.homEquiv (adj.adj Y) M E).symm g := by
  let : IsFibrant ((G.obj (Opposite.op Y)).obj E) :=
    Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj.adj Y) inferInstance
  obtain ⟨g, rfl⟩ := map_surjective_of_isLocalization (toHomotopyCategory P) M
    ((G.obj (Opposite.op Y)).obj E) g
  rw [← (toHomotopyCategory P).map_comp,
    QuillenOrdinaryHoHom.homEquiv_symm_map, QuillenOrdinaryHoHom.homEquiv_symm_map]
  have h := ParametrizedAdjunction.homEquiv_symm_naturality_one adj f g
  rw [ParametrizedAdjunction.homEquiv_eq, ParametrizedAdjunction.homEquiv_eq] at h
  rw [h, (toHomotopyCategory D).map_comp]

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev pointedHo := toHomotopyCategory PointedCGWH.{u, v}
private abbrev diagramHo := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)

private abbrev nativeMappingAdjunction :=
  PointedCGWH.NativeOriginalParametrizedMapping.adjunction (I := I)

private theorem param_isQuillen (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    [IsCofibrant X] : (nativeMappingAdjunction.adj X).IsQuillenAdjunction := by
  rw [PointedCGWH.NativeOriginalParametrizedMapping.fixed]
  exact PointedCGWH.EnrichedIntervalCylinderModel.coefficient_isQuillen X

/-- The two actual Quillen adjunctions identify scalar Hom tests of the original
mapping end with native Hom tests into the original scalar cotensor. -/
def scalarMappingHoEquiv (M : PointedCGWH.{u, v}) [IsCofibrant M]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X]
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ((toHomotopyCategory PointedCGWH.{u, v}).obj M ⟶
      (toHomotopyCategory PointedCGWH.{u, v}).obj (mappingObject X E)) ≃
      ((toHomotopyCategory
        (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X ⟶ (toHomotopyCategory
        (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj ((cotensor M).obj E)) := by
  letI : IsFibrant E := Native.allObjectsFibrant E
  letI : ((PointedCGWH.NativeOriginalParametrizedMapping.adjunction
    (I := I)).adj X).IsQuillenAdjunction := by exact param_isQuillen X
  letI : (ScalarLeibniz.adjunction M (A := I)).IsQuillenAdjunction :=
    ScalarCompatibility.scalar_isQuillen M
  exact (QuillenOrdinaryHoHom.homEquiv ((PointedCGWH.NativeOriginalParametrizedMapping.adjunction
    (I := I)).adj X) M E).symm.trans
    (QuillenOrdinaryHoHom.homEquiv (ScalarLeibniz.adjunction M) X E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every represented scalar Hom has the two original adjunct maps. -/
theorem scalarMappingHoEquiv_map (M : PointedCGWH.{u, v}) [IsCofibrant M]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X]
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) (g : M ⟶ mappingObject X E) :
    scalarMappingHoEquiv M X E ((toHomotopyCategory PointedCGWH.{u, v}).map g) =
      (toHomotopyCategory
        (EnrichedFunctorCat PointedCGWH.{u, v} I)).map ((ScalarLeibniz.adjunction M).homEquiv X E
        ((((PointedCGWH.NativeOriginalParametrizedMapping.adjunction
          (I := I)).adj X).homEquiv M E).symm g)) := by
  let : IsFibrant E := Native.allObjectsFibrant E
  let : ((PointedCGWH.NativeOriginalParametrizedMapping.adjunction
    (I := I)).adj X).IsQuillenAdjunction := by exact param_isQuillen X
  let : (ScalarLeibniz.adjunction M (A := I)).IsQuillenAdjunction :=
    ScalarCompatibility.scalar_isQuillen M
  change QuillenOrdinaryHoHom.homEquiv (ScalarLeibniz.adjunction M) X E
    ((QuillenOrdinaryHoHom.homEquiv ((PointedCGWH.NativeOriginalParametrizedMapping.adjunction
      (I := I)).adj X) M E).symm ((toHomotopyCategory PointedCGWH.{u, v}).map g)) = _
  have h := QuillenOrdinaryHoHom.homEquiv_symm_map
    ((PointedCGWH.NativeOriginalParametrizedMapping.adjunction (I := I)).adj X) M E g
  exact (congrArg (QuillenOrdinaryHoHom.homEquiv (ScalarLeibniz.adjunction M) X E) h).trans
    (QuillenOrdinaryHoHom.homEquiv_map (ScalarLeibniz.adjunction M) X E
      ((((PointedCGWH.NativeOriginalParametrizedMapping.adjunction
        (I := I)).adj X).homEquiv M E).symm g))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source naturality retains the original full weight map and the original native arrow. -/
theorem scalarMappingHoEquiv_source (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (g : (toHomotopyCategory PointedCGWH.{u, v}).obj M ⟶
      (toHomotopyCategory PointedCGWH.{u, v}).obj (mappingObject Y E)) :
    scalarMappingHoEquiv M X E
        (g ≫ (toHomotopyCategory PointedCGWH.{u, v}).map (WeightedEndVariance.pre f E)) =
      (toHomotopyCategory
        (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ scalarMappingHoEquiv M Y E g := by
  let : IsFibrant E := Native.allObjectsFibrant E
  let : ((PointedCGWH.NativeOriginalParametrizedMapping.adjunction
    (I := I)).adj X).IsQuillenAdjunction := by exact param_isQuillen X
  let : ((PointedCGWH.NativeOriginalParametrizedMapping.adjunction
    (I := I)).adj Y).IsQuillenAdjunction := by exact param_isQuillen Y
  let : (ScalarLeibniz.adjunction M (A := I)).IsQuillenAdjunction :=
    ScalarCompatibility.scalar_isQuillen M
  have h := inverseMappingHo_parameter (PointedCGWH.NativeOriginalParametrizedMapping.adjunction
    (I := I)) f M E g
  change (QuillenOrdinaryHoHom.homEquiv ((PointedCGWH.NativeOriginalParametrizedMapping.adjunction
    (I := I)).adj X) M E).symm
      (g ≫ (toHomotopyCategory PointedCGWH.{u, v}).map (WeightedEndVariance.pre f E)) =
    (toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).map ((EnrichedFunctorCat.tensorLeft M).map f) ≫
      (QuillenOrdinaryHoHom.homEquiv ((PointedCGWH.NativeOriginalParametrizedMapping.adjunction
        (I := I)).adj Y) M E).symm g at h
  change QuillenOrdinaryHoHom.homEquiv (ScalarLeibniz.adjunction M) X E
      ((QuillenOrdinaryHoHom.homEquiv ((PointedCGWH.NativeOriginalParametrizedMapping.adjunction
        (I := I)).adj X) M E).symm
        (g ≫ (toHomotopyCategory PointedCGWH.{u, v}).map (WeightedEndVariance.pre f E))) = _
  rw [h]
  exact QuillenOrdinaryHoHom.homEquiv_naturality_left (ScalarLeibniz.adjunction M) E f _

open OperatorStabilizationK

/-- Omega Hom tests imply every cofibrant scalar Hom test of the original mapping map. -/
theorem mappingPostcomp_bijective_of_tests
    {L : Type} (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y)
    (hf : NativeK.omegaTests s f) (E : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (hE : NativeK.IsOmega s E) (M : PointedCGWH.{u, v}) [IsCofibrant M] :
    Function.Bijective (fun g : (toHomotopyCategory PointedCGWH.{u, v}).obj M ⟶
        (toHomotopyCategory PointedCGWH.{u, v}).obj (mappingObject Y E) =>
      g ≫ (toHomotopyCategory PointedCGWH.{u, v}).map (WeightedEndVariance.pre f E)) := by
  have hTests := hf ((cotensor M).obj E) (NativeK.cotensor_isOmega s M E hE)
  constructor
  · intro g g' h
    apply (scalarMappingHoEquiv M Y E).injective
    apply hTests.1
    change (toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ scalarMappingHoEquiv M Y E g =
      (toHomotopyCategory
        (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ scalarMappingHoEquiv M Y E g'
    rw [← scalarMappingHoEquiv_source M f E g,
      ← scalarMappingHoEquiv_source M f E g']
    exact congrArg (scalarMappingHoEquiv M X E) h
  · intro h
    obtain ⟨k, hk⟩ := hTests.2 (scalarMappingHoEquiv M X E h)
    refine ⟨(scalarMappingHoEquiv M Y E).symm k, ?_⟩
    apply (scalarMappingHoEquiv M X E).injective
    rw [scalarMappingHoEquiv_source M f E, Equiv.apply_symm_apply]
    exact hk

omit B in
private theorem weak_of_cofibrant_postcomposition_bijective
    {X Y : PointedCGWH.{u, v}} (p : X ⟶ Y)
    (h : ∀ M : PointedCGWH.{u, v}, IsCofibrant M →
      Function.Bijective (fun g : (toHomotopyCategory PointedCGWH.{u, v}).obj M ⟶
          (toHomotopyCategory PointedCGWH.{u, v}).obj X =>
        g ≫ (toHomotopyCategory PointedCGWH.{u, v}).map p)) :
    weakEquivalences PointedCGWH.{u, v} p := by
  let qX := CofibrantObject.HoCat.pResolutionObj X
  let qY := CofibrantObject.HoCat.pResolutionObj Y
  let : IsIso ((toHomotopyCategory PointedCGWH.{u, v}).map qX) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map qX).mp (mem_weakEquivalences qX)
  let : IsIso ((toHomotopyCategory PointedCGWH.{u, v}).map qY) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map qY).mp (mem_weakEquivalences qY)
  have hX := h (CofibrantObject.HoCat.resolutionObj X) inferInstance
  have hY := h (CofibrantObject.HoCat.resolutionObj Y) inferInstance
  obtain ⟨g, hg⟩ := hY.2 ((toHomotopyCategory PointedCGWH.{u, v}).map qY)
  change g ≫ (toHomotopyCategory PointedCGWH.{u, v}).map p =
    (toHomotopyCategory PointedCGWH.{u, v}).map qY at hg
  let i := inv ((toHomotopyCategory PointedCGWH.{u, v}).map qY) ≫ g
  have hi : i ≫ (toHomotopyCategory PointedCGWH.{u, v}).map p =
      𝟙 ((toHomotopyCategory PointedCGWH.{u, v}).obj Y) := by
    change (inv ((toHomotopyCategory PointedCGWH.{u, v}).map qY) ≫ g) ≫
      (toHomotopyCategory PointedCGWH.{u, v}).map p = _
    rw [Category.assoc, hg, IsIso.inv_hom_id]
  have hp : (toHomotopyCategory PointedCGWH.{u, v}).map p ≫ i =
      𝟙 ((toHomotopyCategory PointedCGWH.{u, v}).obj X) := by
    apply (cancel_epi ((toHomotopyCategory PointedCGWH.{u, v}).map qX)).mp
    apply hX.1
    change ((toHomotopyCategory PointedCGWH.{u, v}).map qX ≫
        (toHomotopyCategory PointedCGWH.{u, v}).map p ≫ i) ≫
        (toHomotopyCategory PointedCGWH.{u, v}).map p =
      ((toHomotopyCategory PointedCGWH.{u, v}).map qX ≫
        𝟙 ((toHomotopyCategory PointedCGWH.{u, v}).obj X)) ≫
        (toHomotopyCategory PointedCGWH.{u, v}).map p
    rw [Category.assoc, Category.assoc, hi, Category.comp_id, Category.comp_id]
  let e : (toHomotopyCategory PointedCGWH.{u, v}).obj X ≅
      (toHomotopyCategory PointedCGWH.{u, v}).obj Y :=
    { hom := (toHomotopyCategory PointedCGWH.{u, v}).map p
      inv := i
      hom_inv_id := hp
      inv_hom_id := hi }
  exact (weakEquivalence_iff_isIso_toHomotopyCategory_map p).mpr e.isIso_hom

/-- Two actual cofibrant resolutions turn all scalar Hom tests into weakness of
the complete original mapping map. -/
theorem mappingPre_weak_of_omegaTests
    {L : Type} (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) (hf : NativeK.omegaTests s f)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) (hE : NativeK.IsOmega s E) :
    weakEquivalences PointedCGWH.{u, v} (WeightedEndVariance.pre f E) := by
  apply weak_of_cofibrant_postcomposition_bijective
  intro M hM
  let : IsCofibrant M := hM
  exact mappingPostcomp_bijective_of_tests s f hf E hE M

/-- At the native smash unit the original cotensor evaluation identifies the
mapping-point Hom with the native ordinary Hom. -/
def pointMappingHoEquiv
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X]
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ((toHomotopyCategory PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}) ⟶
      (toHomotopyCategory PointedCGWH.{u, v}).obj (mappingObject X E)) ≃
      ((toHomotopyCategory
        (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X ⟶ (toHomotopyCategory
        (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj E) := by
  let : IsCofibrant (𝟙_ PointedCGWH.{u, v}) := PointedCGWH.modelCategory.smashUnit_isCofibrant
  let e := (toHomotopyCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} I)).mapIso
      (NativeOmegaRecovery.OriginalCotensorUnit.iso E)
  exact (scalarMappingHoEquiv (𝟙_ PointedCGWH.{u, v}) X E).trans
    { toFun := fun g => g ≫ e.hom
      invFun := fun g => g ≫ e.inv
      left_inv := fun g => by
        change (g ≫ e.hom) ≫ e.inv = g
        rw [Category.assoc, e.hom_inv_id, Category.comp_id]
      right_inv := fun g => by
        change (g ≫ e.inv) ≫ e.hom = g
        rw [Category.assoc, e.inv_hom_id, Category.comp_id] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original point-Hom correspondence is natural in the full native source arrow. -/
theorem pointMappingHoEquiv_source
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (g : (toHomotopyCategory PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}) ⟶
      (toHomotopyCategory PointedCGWH.{u, v}).obj (mappingObject Y E)) :
    pointMappingHoEquiv X E
        (g ≫ (toHomotopyCategory PointedCGWH.{u, v}).map (WeightedEndVariance.pre f E)) =
      (toHomotopyCategory
        (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ pointMappingHoEquiv Y E g := by
  let : IsCofibrant (𝟙_ PointedCGWH.{u, v}) := PointedCGWH.modelCategory.smashUnit_isCofibrant
  change scalarMappingHoEquiv (𝟙_ PointedCGWH.{u, v}) X E
      (g ≫ (toHomotopyCategory PointedCGWH.{u, v}).map (WeightedEndVariance.pre f E)) ≫
        (toHomotopyCategory
          (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          (NativeOmegaRecovery.OriginalCotensorUnit.iso E).hom =
    (toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫
      scalarMappingHoEquiv (𝟙_ PointedCGWH.{u, v}) Y E g ≫
      (toHomotopyCategory
        (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        (NativeOmegaRecovery.OriginalCotensorUnit.iso E).hom
  rw [scalarMappingHoEquiv_source, Category.assoc]

/-- Weakness of the full mapping maps recovers every original Omega-target Hom test. -/
theorem omegaTests_of_mappingPre_weak
    {L : Type} (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y)
    (hf : ∀ E : EnrichedFunctorCat PointedCGWH.{u, v} I, NativeK.IsOmega s E →
      weakEquivalences PointedCGWH.{u, v} (WeightedEndVariance.pre f E)) :
    NativeK.omegaTests s f := by
  intro E hE
  have hIso := (weakEquivalence_iff_isIso_toHomotopyCategory_map
    (WeightedEndVariance.pre f E)).mp (hf E hE)
  have hBij := (isIso_iff_yoneda_map_bijective _).mp hIso
    ((toHomotopyCategory PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
  constructor
  · intro g g' h
    apply (pointMappingHoEquiv Y E).symm.injective
    apply hBij.1
    change (pointMappingHoEquiv Y E).symm g ≫
        (toHomotopyCategory PointedCGWH.{u, v}).map (WeightedEndVariance.pre f E) =
      (pointMappingHoEquiv Y E).symm g' ≫
        (toHomotopyCategory PointedCGWH.{u, v}).map (WeightedEndVariance.pre f E)
    apply (pointMappingHoEquiv X E).injective
    rw [pointMappingHoEquiv_source, pointMappingHoEquiv_source,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h
  · intro g
    obtain ⟨k, hk⟩ := hBij.2 ((pointMappingHoEquiv X E).symm g)
    refine ⟨pointMappingHoEquiv Y E k, ?_⟩
    change (toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ pointMappingHoEquiv Y E k = g
    rw [← pointMappingHoEquiv_source]
    change k ≫ (toHomotopyCategory PointedCGWH.{u, v}).map (WeightedEndVariance.pre f E) =
      (pointMappingHoEquiv X E).symm g at hk
    rw [hk, Equiv.apply_symm_apply]

/-- On cofibrant sources the complete strict mapping-space criterion is exactly
the original native Omega Hom-test class. -/
theorem omegaTests_iff_mappingPre_weak
    {L : Type} (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    NativeK.omegaTests s f ↔
      ∀ E : EnrichedFunctorCat PointedCGWH.{u, v} I, NativeK.IsOmega s E →
        weakEquivalences PointedCGWH.{u, v} (WeightedEndVariance.pre f E) :=
  ⟨fun hf E hE => mappingPre_weak_of_omegaTests s f hf E hE,
    omegaTests_of_mappingPre_weak s f⟩

/-- The framework's actual cofibrant counit square preserves and reflects the
original Omega tests on arbitrary arrows. -/
theorem omegaTests_cofibrantReplacement_map_iff
    {L : Type} (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    NativeK.omegaTests s ((cofibrantReplacement
      (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).map f) ↔ NativeK.omegaTests s f := by
  let Q := cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
  let ε := cofibrantReplacementCounit (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
  have hX := NativeK.levelWeak_le_omegaTests s (ε.app X) (mem_weakEquivalences _)
  have hY := NativeK.levelWeak_le_omegaTests s (ε.app Y) (mem_weakEquivalences _)
  have hNat : Q.map f ≫ ε.app Y = ε.app X ≫ f := ε.naturality f
  constructor
  · intro h
    have hComp := (NativeK.omegaTests s).comp_mem _ _ h hY
    rw [hNat] at hComp
    exact (NativeK.omegaTests s).of_precomp _ _ hX hComp
  · intro h
    have hComp := (NativeK.omegaTests s).comp_mem _ _ hX h
    rw [← hNat] at hComp
    exact (NativeK.omegaTests s).of_postcomp _ _ hY hComp

attribute [local instance] SimplicialEnrichment.simplicialCategory

/-- The actual fibrant unit compares the chosen derived map with the complete
strict map of the actual cofibrant replacement arrow. -/
theorem derivedPrecomp_weak_iff_cofibrantReplacement_strict
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    SSet.realizationWeakEquivalences
        (derivedMappingPrecomp (C := EnrichedFunctorCat PointedCGWH.{u, v} I) f E) ↔
      SSet.realizationWeakEquivalences
        (((SimplicialCategory.sHomFunctor (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          ((cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).map f).op).app
            E) := by
  let Q := cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
  let η := fibrantReplacementUnit (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
  let F := SimplicialCategory.sHomFunctor (EnrichedFunctorCat PointedCGWH.{u, v} I)
  have hX := SingularMapping.target_weak (Q.obj X) (η.app E) (mem_weakEquivalences _)
  have hY := SingularMapping.target_weak (Q.obj Y) (η.app E) (mem_weakEquivalences _)
  have hNat := ((F.map (Q.map f).op).naturality (η.app E)).symm
  change (F.map (Q.map f).op).app E ≫ (F.obj (Opposite.op (Q.obj X))).map (η.app E) =
    (F.obj (Opposite.op (Q.obj Y))).map (η.app E) ≫
      derivedMappingPrecomp (C := EnrichedFunctorCat PointedCGWH.{u, v} I) f E at hNat
  constructor
  · intro h
    have hComp := SSet.realizationWeakEquivalences.comp_mem _ _ hY h
    rw [← hNat] at hComp
    exact SSet.realizationWeakEquivalences.of_postcomp _ _ hX hComp
  · intro h
    have hComp := SSet.realizationWeakEquivalences.comp_mem _ _ h hX
    rw [hNat] at hComp
    exact SSet.realizationWeakEquivalences.of_precomp _ _ hY hComp

/-- For arbitrary native arrows, all chosen derived mapping tests against
original Omega targets are exactly the original native Hom tests. -/
theorem omegaTests_iff_derivedPrecomp_weak
    {L : Type} (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    NativeK.omegaTests s f ↔
      ∀ E : EnrichedFunctorCat PointedCGWH.{u, v} I, NativeK.IsOmega s E →
        SSet.realizationWeakEquivalences
          (derivedMappingPrecomp (C := EnrichedFunctorCat PointedCGWH.{u, v} I) f E) := by
  let Q := cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
  constructor
  · intro hf E hE
    apply (derivedPrecomp_weak_iff_cofibrantReplacement_strict f E).mpr
    rw [SimplicialEnrichment.source_map]
    apply (SingularMapping.singularFunctor_weak_iff _).mpr
    exact mappingPre_weak_of_omegaTests s (Q.map f)
      ((omegaTests_cofibrantReplacement_map_iff s f).mpr hf) E hE
  · intro hf
    apply (omegaTests_cofibrantReplacement_map_iff s f).mp
    apply omegaTests_of_mappingPre_weak s (Q.map f)
    intro E hE
    have h := (derivedPrecomp_weak_iff_cofibrantReplacement_strict f E).mp (hf E hE)
    rw [SimplicialEnrichment.source_map] at h
    exact (SingularMapping.singularFunctor_weak_iff _).mp h

/-- Derived locality for the whole original stabilization Arrow family gives
exactly the original native Omega Hom-test class on every arrow. -/
theorem localEquivalences_eq_omegaTests
    {L : Type} (s : NativeStabilizationFamily.{u, v} I L) :
    localEquivalences (DerivedLocalMapping.stabilizationArrows s) = NativeK.omegaTests s := by
  ext X Y f
  constructor
  · intro h
    apply (omegaTests_iff_derivedPrecomp_weak s f).mpr
    intro E hE
    exact h E ((DerivedLocalMapping.isLocalFibrant_iff_isOmega s E).mpr hE)
  · intro h E hE
    exact (omegaTests_iff_derivedPrecomp_weak s f).mp h E
      ((DerivedLocalMapping.isLocalFibrant_iff_isOmega s E).mp hE)

/-- Actual index-Hom cofibrancy and the original all-source cell proof make
the whole original K-left class derived locally weak. -/
theorem KLeft_le_localEquivalences
    {L : Type} (s : NativeStabilizationFamily.{u, v} I L)
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    (NativeK.generators s).rlp.llp ≤ localEquivalences (stabilizationArrows s) := by
  rw [localEquivalences_eq_omegaTests]
  exact NativeK.originalKLeft_le_localTests s hHom

/-- Every original K generator, including its full horn and paired scalar
boundary branches, is a derived local equivalence. -/
theorem generators_le_localEquivalences
    {L : Type} (s : NativeStabilizationFamily.{u, v} I L)
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    NativeK.generators s ≤ localEquivalences (stabilizationArrows s) :=
  (NativeK.generators s).le_llp_rlp.trans (KLeft_le_localEquivalences s hHom)

end HomotopicalAlgebra.EnrichedProjective.Native.DerivedLocalMapping

namespace HomotopicalAlgebra.EnrichedProjective.Native.DerivedLocalMapping

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory PointedCGWH.EnrichedMapping.hasSmallLimits


private theorem Ho_precomp_bijective_of_mappingPre_weak
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (hf : weakEquivalences PointedCGWH.{u, v} (WeightedEndVariance.pre f E)) :
    Function.Bijective (fun g : (toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y ⟶ (toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj E => (toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ g) := by
  have hIso := (weakEquivalence_iff_isIso_toHomotopyCategory_map
    (WeightedEndVariance.pre f E)).mp hf
  have hBij := (isIso_iff_yoneda_map_bijective _).mp hIso
    ((toHomotopyCategory PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
  constructor
  · intro g g' h
    apply (pointMappingHoEquiv Y E).symm.injective
    apply hBij.1
    change (pointMappingHoEquiv Y E).symm g ≫
        (toHomotopyCategory PointedCGWH.{u, v}).map (WeightedEndVariance.pre f E) =
      (pointMappingHoEquiv Y E).symm g' ≫
        (toHomotopyCategory PointedCGWH.{u, v}).map (WeightedEndVariance.pre f E)
    apply (pointMappingHoEquiv X E).injective
    rw [pointMappingHoEquiv_source, pointMappingHoEquiv_source,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h
  · intro g
    obtain ⟨k, hk⟩ := hBij.2 ((pointMappingHoEquiv X E).symm g)
    refine ⟨pointMappingHoEquiv Y E k, ?_⟩
    change (toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ pointMappingHoEquiv Y E k = g
    rw [← pointMappingHoEquiv_source]
    change k ≫ (toHomotopyCategory PointedCGWH.{u, v}).map (WeightedEndVariance.pre f E) =
      (pointMappingHoEquiv X E).symm g at hk
    rw [hk, Equiv.apply_symm_apply]

private theorem weak_of_mappingPre_weak_allTargets
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y)
    (hf : ∀ E : EnrichedFunctorCat PointedCGWH.{u, v} I,
      weakEquivalences PointedCGWH.{u, v} (WeightedEndVariance.pre f E)) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f := by
  have hX := Ho_precomp_bijective_of_mappingPre_weak f X (hf X)
  have hY := Ho_precomp_bijective_of_mappingPre_weak f Y (hf Y)
  obtain ⟨g, hfg⟩ := hX.2 (𝟙 ((toHomotopyCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X))
  change (toHomotopyCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ g = 𝟙 ((toHomotopyCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X) at hfg
  have hgf : g ≫ (toHomotopyCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f = 𝟙 ((toHomotopyCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y) := by
    apply hY.1
    change (toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ (g ≫ (toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f) = (toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f ≫ 𝟙 ((toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y)
    rw [← Category.assoc, hfg, Category.id_comp, Category.comp_id]
  let e : (toHomotopyCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X ≅ (toHomotopyCategory
    (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Y :=
    { hom := (toHomotopyCategory
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f
      inv := g
      hom_inv_id := hfg
      inv_hom_id := hgf }
  exact (weakEquivalence_iff_isIso_toHomotopyCategory_map f).mpr e.isIso_hom

private theorem weakEquivalence_iff_derivedPrecomp_allFibrant
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f ↔
      ∀ E : EnrichedFunctorCat PointedCGWH.{u, v} I, IsFibrant E →
        SSet.realizationWeakEquivalences (derivedMappingPrecomp f E) := by
  let Q := cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
  let R := fibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
  let ε := cofibrantReplacementCounit (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
  have hX : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) (ε.app X) :=
    mem_weakEquivalences _
  have hY : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) (ε.app Y) :=
    mem_weakEquivalences _
  have hNat : Q.map f ≫ ε.app Y = ε.app X ≫ f := ε.naturality f
  constructor
  · intro hf E _hE
    have hQf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) (Q.map f) := by
      apply (weakEquivalences _).of_postcomp _ _ hY
      rw [hNat]
      exact (weakEquivalences _).comp_mem _ _ hX hf
    exact SingularMapping.source_weak (Q.map f) hQf (R.obj E)
  · intro hf
    have hQf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) (Q.map f) := by
      apply weak_of_mappingPre_weak_allTargets
      intro E
      have h := (derivedPrecomp_weak_iff_cofibrantReplacement_strict f E).mp
        (hf E (Native.allObjectsFibrant E))
      rw [SimplicialEnrichment.source_map] at h
      exact (SingularMapping.singularFunctor_weak_iff _).mp h
    have hComp := (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)).comp_mem
      _ _ hQf hY
    rw [hNat] at hComp
    exact (weakEquivalences _).of_precomp _ _ hX hComp

/-- The strict simplicial mapping bifunctor at the framework's actual cofibrant replacement. -/
def cofibrantStrictMappingObject :
    (EnrichedFunctorCat PointedCGWH.{u, v} I)ᵒᵖ ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} I ⥤ SSet.{v} :=
  (cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).op ⋙
    SimplicialCategory.sHomFunctor (EnrichedFunctorCat PointedCGWH.{u, v} I)

/-- The alternative presentation is singularization of the original full weighted end
at that same actual cofibrant replacement, with no target replacement. -/
def nativeCofibrantMappingObject :
    (EnrichedFunctorCat PointedCGWH.{u, v} I)ᵒᵖ ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} I ⥤ SSet.{v} :=
  (cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).op ⋙
    SimplicialEnrichment.singularMappingFunctor (I := I)

/-- The whole native mapping-functor comparison is whiskered by the actual source replacement. -/
def nativeCofibrantMappingIso :
    cofibrantStrictMappingObject (I := I) ≅ nativeCofibrantMappingObject (I := I) :=
  Functor.isoWhiskerLeft
    (cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).op
    (SimplicialEnrichment.mappingFunctorIso (I := I))

set_option backward.isDefEq.respectTransparency false in
/-- The original fibrant unit gives the whole comparison to the chosen derived mapping
bifunctor, natural in both original source and target arrows. -/
def cofibrantMappingToDerived : cofibrantStrictMappingObject (I := I) ⟶
    derivedMappingObject (C := EnrichedFunctorCat PointedCGWH.{u, v} I) where
  app X :=
    { app E :=
        ((SimplicialCategory.sHomFunctor (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
          ((cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).op.obj X)).map
            ((fibrantReplacementUnit (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).app E)
      naturality E E' g := by
        let F := (SimplicialCategory.sHomFunctor (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
          ((cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).op.obj X)
        let η := fibrantReplacementUnit (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
        let R := fibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
        change F.map g ≫ F.map (η.app E') = F.map (η.app E) ≫ F.map (R.map g)
        rw [← F.map_comp, ← F.map_comp]
        exact congrArg F.map (η.naturality g) }
  naturality X X' f := by
    apply NatTrans.ext
    funext E
    let Q := cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
    let F := SimplicialCategory.sHomFunctor (EnrichedFunctorCat PointedCGWH.{u, v} I)
    let η := fibrantReplacementUnit (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
    change (F.map (Q.op.map f)).app E ≫ (F.obj (Q.op.obj X')).map (η.app E) =
      (F.obj (Q.op.obj X)).map (η.app E) ≫
        (F.map (Q.op.map f)).app
          ((fibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).obj E)
    exact ((F.map (Q.op.map f)).naturality (η.app E)).symm

/-- Each derived comparison component is the singularization of the original target map
of the actual chosen fibrant unit. -/
theorem cofibrantMappingToDerived_app
    (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)ᵒᵖ)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ((cofibrantMappingToDerived (I := I)).app X).app E =
      PointedCGWH.SingularHomotopyGeometry.singularFunctor.map
        (WeightedEndVariance.post
          ((cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X.unop)
          ((fibrantReplacementUnit (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).app E)) :=
  SimplicialEnrichment.target_map _ _

/-- Each alternative comparison component is the identity of the complete original mapping end. -/
theorem nativeCofibrantMappingIso_hom_app
    (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)ᵒᵖ)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (((nativeCofibrantMappingIso (I := I)).hom).app X).app E =
      𝟙 (PointedCGWH.SingularHomotopyGeometry.singularFunctor.obj
        (PointedCGWH.EnrichedFunctorMapping.mappingObject
          ((cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X.unop)
          E)) := rfl

/-- Fixed-cofibrant-source native Quillen mapping sends the actual fibrant unit to a weak map. -/
theorem cofibrantMappingToDerived_app_weak
    (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)ᵒᵖ)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    SSet.realizationWeakEquivalences (((cofibrantMappingToDerived (I := I)).app X).app E) :=
  SingularMapping.target_weak
    ((cofibrantReplacement (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X.unop)
    ((fibrantReplacementUnit (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).app E)
    (mem_weakEquivalences _)

/-- Construct the full native function-complex data from the actual original end,
replacement comparison maps, native invariance, and the point-Hom weak detector.
No function-complex or model-compatibility outcome is supplied. -/
def functionComplexData :
    HomotopyFunctionComplexData (C := EnrichedFunctorCat PointedCGWH.{u, v} I) where
  toHomotopyFunctionComplexInvarianceData := SingularMapping.invarianceData
  alternativeMappingObject := nativeCofibrantMappingObject
  comparisonMappingObject := cofibrantStrictMappingObject
  comparisonToDerived := cofibrantMappingToDerived
  comparisonToAlternative := nativeCofibrantMappingIso.hom
  comparisonToDerived_weak := cofibrantMappingToDerived_app_weak
  comparisonToAlternative_weak X E := by
    rw [nativeCofibrantMappingIso_hom_app]
    exact SSet.realizationWeakEquivalences.id_mem _
  weakEquivalence_iff_derivedMappingPrecomp f := by
    exact weakEquivalence_iff_derivedPrecomp_allFibrant f

end HomotopicalAlgebra.EnrichedProjective.Native.DerivedLocalMapping
