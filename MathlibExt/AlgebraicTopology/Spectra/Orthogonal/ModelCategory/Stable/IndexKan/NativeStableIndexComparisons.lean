/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.OmegaHomTestTransport
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKMonoidal
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableGeneratorClasses
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.IntegerGroups
import MathlibExt.CategoryTheory.Enriched.RestrictionInversePair
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.IndexKanComposition
import MathlibExt.Topology.Category.PointedCGWH.SmallKanCoends

/-!
# Original native stable index comparisons

The functors below are the original enriched weighted-coend Kan extensions
and the complete restrictions on the unchanged native spectrum categories.
The actual level adjunctions and original Omega restriction laws give the
stable generator-image argument, with every original horn and correlated
boundary/mapping-cylinder generator retained.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.IndexKan.NativeStableIndexComparisons

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open CategoryTheory.Spectra CategoryTheory.Spectra.SpectrumIndexMaps
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.Spectra.NativeIndexKanComposition
  (sequentialOrthogonalLan symmetricOrthogonalLan sequentialOrthogonalRestriction
    symmetricOrthogonalRestriction sequentialOrthogonalAdjunction symmetricOrthogonalAdjunction)

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

private abbrev OC := OrthogonalCarrier.{u, v}
private abbrev SC := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev YC := SymmetricCarrier.{u, v}
private abbrev sSeq := PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}

private instance nativeKanRelationCoproducts {A : Type}
    [EnrichedCategory PointedCGWH.{u, v} A]
    (j : EnrichedFunctor PointedCGWH.{u, v} A OrthogonalOperatorIndex.{u, v}) :
    ∀ (X : EnrichedFunctorCat PointedCGWH.{u, v} A) (b : OrthogonalOperatorIndex.{u, v}),
      HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor) :=
  fun X b => PointedCGWH.EnrichedKan.hasRelationCoproduct
    (leftKanWeight j b) X.toEnrichedFunctor

private instance nativeKanObjectCoproducts {A : Type}
    [EnrichedCategory PointedCGWH.{u, v} A]
    (j : EnrichedFunctor PointedCGWH.{u, v} A OrthogonalOperatorIndex.{u, v}) :
    ∀ (X : EnrichedFunctorCat PointedCGWH.{u, v} A) (b : OrthogonalOperatorIndex.{u, v}),
      HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor) :=
  fun X b => PointedCGWH.EnrichedKan.hasObjectCoproduct
    (leftKanWeight j b) X.toEnrichedFunctor

private instance nativeKanCoequalizers {A : Type}
    [EnrichedCategory PointedCGWH.{u, v} A]
    (j : EnrichedFunctor PointedCGWH.{u, v} A OrthogonalOperatorIndex.{u, v}) :
    ∀ (X : EnrichedFunctorCat PointedCGWH.{u, v} A) (b : OrthogonalOperatorIndex.{u, v}),
      HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
        (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor) :=
  fun X b => PointedCGWH.EnrichedKan.hasBalancingCoequalizer
    (leftKanWeight j b) X.toEnrichedFunctor

/-- Both complete original restrictions compose to the same sequential functor,
including every original full Hom action and every transformation component. -/
theorem symmetricRestriction_comp_underlyingSequential :
    symmetricOrthogonalRestriction.{u, v} ⋙ SymmetricIntegerHomotopy.underlyingSequential =
      sequentialOrthogonalRestriction :=
  EnrichedFunctorCat.RestrictionInversePair.restriction_comp sequentialSymmetricOperatorIndexFunctor
    symmetricOrthogonalOperatorIndexFunctor

/-- Restriction retains the entire original integer group functor, on all native arrows. -/
theorem symmetricRestriction_integerPiFunctor (q : ℤ) :
    symmetricOrthogonalRestriction.{u, v} ⋙ SymmetricIntegerHomotopy.integerPiFunctor q =
      OrthogonalIntegerHomotopy.integerPiFunctor q := by
  change symmetricOrthogonalRestriction ⋙
      (SymmetricIntegerHomotopy.underlyingSequential ⋙
        integerStablePiFunctor q) =
    sequentialOrthogonalRestriction ⋙ integerStablePiFunctor q
  rw [← Functor.assoc, symmetricRestriction_comp_underlyingSequential]

/-- Each complete original integer group map keeps both actual object transports. -/
theorem symmetricRestriction_integerPiFunctor_map (q : ℤ) {X Y : OC.{u, v}} (f : X ⟶ Y) :
    (SymmetricIntegerHomotopy.integerPiFunctor q).map (symmetricOrthogonalRestriction.map f) =
      eqToHom (Functor.congr_obj (symmetricRestriction_integerPiFunctor q) X) ≫
        (OrthogonalIntegerHomotopy.integerPiFunctor q).map f ≫
        eqToHom (Functor.congr_obj (symmetricRestriction_integerPiFunctor q) Y).symm :=
  Functor.congr_hom (symmetricRestriction_integerPiFunctor q) f

/-- Every original integer group is tested by the same whole restricted native arrow.
This is an equality of raw integer criteria and asserts no symmetric stable converse. -/
theorem symmetricRestriction_integerPiStar_iff {X Y : OC.{u, v}} (f : X ⟶ Y) :
    SymmetricIntegerHomotopy.integerPiStarEquivalences (symmetricOrthogonalRestriction.map f) ↔
      OrthogonalIntegerHomotopy.integerPiStarEquivalences f := by
  rw [SymmetricIntegerHomotopy.integerPiStarEquivalences_iff,
    OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff]
  exact forall_congr' (fun q =>
    NatIso.isIso_map_iff (eqToIso (symmetricRestriction_integerPiFunctor q)) f)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The original sequential K union is sent to actual orthogonal level
cofibrations satisfying every full original orthogonal Omega Hom test. -/
theorem sequentialGenerator_images {X Y : SC.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.generators sSeq f) :
    cofibrations OC.{u, v} (sequentialOrthogonalLan.map f) ∧
      NativeK.omegaTests orthogonalFamily (sequentialOrthogonalLan.map f) := by
  let hQ := originalAdjunction_isQuillen sequentialOrthogonalOperatorIndexFunctor
  have hEndpoints := NativeK.generatorEndpoints sSeq f hf
  let _ : IsCofibrant X := hEndpoints.1
  let _ : IsCofibrant Y := hEndpoints.2
  have hWeak : NativeK.omegaTests sSeq f :=
    PointedCGWH.Spectra.NativeStable.sequentialKLeft_le_omegaTests f
      ((NativeK.generators sSeq).le_llp_rlp f hf)
  exact ⟨hQ.preservesCofibrations f (NativeK.generators_le_cofibrations sSeq f hf),
    sequentialLan_omegaTests f hWeak⟩

/-- All original symmetric K generators retain their actual coend images,
original level cofibrations, and every orthogonal Omega-target Hom test. -/
theorem symmetricGenerator_images {X Y : YC.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.generators symmetricFamily f) :
    cofibrations OC.{u, v} (symmetricOrthogonalLan.map f) ∧
      NativeK.omegaTests orthogonalFamily (symmetricOrthogonalLan.map f) := by
  let hQ := originalAdjunction_isQuillen symmetricOrthogonalOperatorIndexFunctor
  have hEndpoints := NativeK.generatorEndpoints symmetricFamily f hf
  let _ : IsCofibrant X := hEndpoints.1
  let _ : IsCofibrant Y := hEndpoints.2
  have hWeak : NativeK.omegaTests symmetricFamily f :=
    PointedCGWH.Spectra.NativeStable.symmetricKLeft_le_omegaTests f
      ((NativeK.generators symmetricFamily).le_llp_rlp f hf)
  exact ⟨hQ.preservesCofibrations f (NativeK.generators_le_cofibrations symmetricFamily f hf),
    symmetricLan_omegaTests f hWeak⟩

/-- The actual source I replacement used by the sequential derived comparison. -/
abbrev sequentialOriginalQ : SC.{u, v} ⥤ SC.{u, v} :=
  originalQ (B := B) (A := PointedCGWH.Spectra.Sequential.Index.{u, v})

/-- Its complete original I counit retains every source replacement component. -/
abbrev sequentialOriginalQCounit : sequentialOriginalQ.{u, v} ⟶ 𝟭 SC.{u, v} :=
  originalQCounit (B := B) (A := PointedCGWH.Spectra.Sequential.Index.{u, v})

/-- The actual symmetric source I replacement, before the original coend Lan. -/
abbrev symmetricOriginalQ : YC.{u, v} ⥤ YC.{u, v} :=
  originalQ (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- The symmetric comparison uses the entire unchanged original I counit. -/
abbrev symmetricOriginalQCounit : symmetricOriginalQ.{u, v} ⟶ 𝟭 YC.{u, v} :=
  originalQCounit (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- The target replacement is the genuine original full-family orthogonal K functor. -/
abbrev orthogonalOriginalR : OC.{u, v} ⥤ OC.{u, v} :=
  NativeK.omegaReplacement orthogonalFamily

/-- The original orthogonal K inclusion is the whole target replacement unit. -/
abbrev orthogonalOriginalRUnit : 𝟭 OC.{u, v} ⟶ orthogonalOriginalR.{u, v} :=
  NativeK.omegaReplacementUnit orthogonalFamily

/-- The sequential derived unit keeps the actual I source, coend unit and
restricted original K target-unit map. -/
def sequentialDerivedUnit : sequentialOriginalQ.{u, v} ⟶
    ((sequentialOriginalQ ⋙ sequentialOrthogonalLan) ⋙ orthogonalOriginalR) ⋙ sequentialOrthogonalRestriction where
  app X := sequentialOrthogonalAdjunction.unit.app (sequentialOriginalQ.obj X) ≫
    sequentialOrthogonalRestriction.map
      (orthogonalOriginalRUnit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X)))
  naturality X Y f := by
    change sequentialOriginalQ.map f ≫
        (sequentialOrthogonalAdjunction.unit.app (sequentialOriginalQ.obj Y) ≫
          sequentialOrthogonalRestriction.map
            (orthogonalOriginalRUnit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj Y)))) =
      (sequentialOrthogonalAdjunction.unit.app (sequentialOriginalQ.obj X) ≫
        sequentialOrthogonalRestriction.map
          (orthogonalOriginalRUnit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X)))) ≫
        sequentialOrthogonalRestriction.map (orthogonalOriginalR.map
          (sequentialOrthogonalLan.map (sequentialOriginalQ.map f)))
    have hUnit := sequentialOrthogonalAdjunction.unit.naturality (sequentialOriginalQ.map f)
    have hR := orthogonalOriginalRUnit.naturality
      (sequentialOrthogonalLan.map (sequentialOriginalQ.map f))
    simp only [Functor.id_map, Functor.comp_map] at hUnit hR
    rw [← Category.assoc, hUnit, Category.assoc,
      ← sequentialOrthogonalRestriction.map_comp, hR,
      sequentialOrthogonalRestriction.map_comp, Category.assoc]

/-- The symmetric derived unit retains the same actual source-Q and target-K choices. -/
def symmetricDerivedUnit : symmetricOriginalQ.{u, v} ⟶
    ((symmetricOriginalQ ⋙ symmetricOrthogonalLan) ⋙ orthogonalOriginalR) ⋙ symmetricOrthogonalRestriction where
  app X := symmetricOrthogonalAdjunction.unit.app (symmetricOriginalQ.obj X) ≫
    symmetricOrthogonalRestriction.map
      (orthogonalOriginalRUnit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X)))
  naturality X Y f := by
    change symmetricOriginalQ.map f ≫
        (symmetricOrthogonalAdjunction.unit.app (symmetricOriginalQ.obj Y) ≫
          symmetricOrthogonalRestriction.map
            (orthogonalOriginalRUnit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj Y)))) =
      (symmetricOrthogonalAdjunction.unit.app (symmetricOriginalQ.obj X) ≫
        symmetricOrthogonalRestriction.map
          (orthogonalOriginalRUnit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X)))) ≫
        symmetricOrthogonalRestriction.map (orthogonalOriginalR.map
          (symmetricOrthogonalLan.map (symmetricOriginalQ.map f)))
    have hUnit := symmetricOrthogonalAdjunction.unit.naturality (symmetricOriginalQ.map f)
    have hR := orthogonalOriginalRUnit.naturality
      (symmetricOrthogonalLan.map (symmetricOriginalQ.map f))
    simp only [Functor.id_map, Functor.comp_map] at hUnit hR
    rw [← Category.assoc, hUnit, Category.assoc,
      ← symmetricOrthogonalRestriction.map_comp, hR,
      symmetricOrthogonalRestriction.map_comp, Category.assoc]

/-- The actual sequential derived counit contracts the original Lan-Q of
the complete restriction of the original target K replacement. -/
def sequentialDerivedCounit :
    ((orthogonalOriginalR.{u, v} ⋙ sequentialOrthogonalRestriction) ⋙ sequentialOriginalQ) ⋙ sequentialOrthogonalLan ⟶
      orthogonalOriginalR where
  app E := sequentialOrthogonalLan.map (sequentialOriginalQCounit.app
      (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj E))) ≫
    sequentialOrthogonalAdjunction.counit.app (orthogonalOriginalR.obj E)
  naturality X Y f := by
    change sequentialOrthogonalLan.map (sequentialOriginalQ.map
        (sequentialOrthogonalRestriction.map (orthogonalOriginalR.map f))) ≫
        (sequentialOrthogonalLan.map (sequentialOriginalQCounit.app
          (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj Y))) ≫
            sequentialOrthogonalAdjunction.counit.app (orthogonalOriginalR.obj Y)) =
      (sequentialOrthogonalLan.map (sequentialOriginalQCounit.app
        (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj X))) ≫
          sequentialOrthogonalAdjunction.counit.app (orthogonalOriginalR.obj X)) ≫
            orthogonalOriginalR.map f
    have hQ := sequentialOriginalQCounit.naturality
      (sequentialOrthogonalRestriction.map (orthogonalOriginalR.map f))
    have hCounit := sequentialOrthogonalAdjunction.counit.naturality (orthogonalOriginalR.map f)
    simp only [Functor.id_map, Functor.comp_map] at hQ hCounit
    rw [← Category.assoc, ← sequentialOrthogonalLan.map_comp,
      hQ, sequentialOrthogonalLan.map_comp, Category.assoc, hCounit, Category.assoc]

/-- The whole symmetric derived counit uses the unchanged I-Q counit,
the genuine coend map and its original counit at the actual K target. -/
def symmetricDerivedCounit :
    ((orthogonalOriginalR.{u, v} ⋙ symmetricOrthogonalRestriction) ⋙ symmetricOriginalQ) ⋙ symmetricOrthogonalLan ⟶
      orthogonalOriginalR where
  app E := symmetricOrthogonalLan.map (symmetricOriginalQCounit.app
      (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj E))) ≫
    symmetricOrthogonalAdjunction.counit.app (orthogonalOriginalR.obj E)
  naturality X Y f := by
    change symmetricOrthogonalLan.map (symmetricOriginalQ.map
        (symmetricOrthogonalRestriction.map (orthogonalOriginalR.map f))) ≫
        (symmetricOrthogonalLan.map (symmetricOriginalQCounit.app
          (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj Y))) ≫
            symmetricOrthogonalAdjunction.counit.app (orthogonalOriginalR.obj Y)) =
      (symmetricOrthogonalLan.map (symmetricOriginalQCounit.app
        (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj X))) ≫
          symmetricOrthogonalAdjunction.counit.app (orthogonalOriginalR.obj X)) ≫
            orthogonalOriginalR.map f
    have hQ := symmetricOriginalQCounit.naturality
      (symmetricOrthogonalRestriction.map (orthogonalOriginalR.map f))
    have hCounit := symmetricOrthogonalAdjunction.counit.naturality (orthogonalOriginalR.map f)
    simp only [Functor.id_map, Functor.comp_map] at hQ hCounit
    rw [← Category.assoc, ← symmetricOrthogonalLan.map_comp,
      hQ, symmetricOrthogonalLan.map_comp, Category.assoc, hCounit, Category.assoc]

/-- Every original source has the same entire sequential derived-unit component. -/
theorem sequentialDerivedUnit_app (X : SC.{u, v}) :
    sequentialDerivedUnit.app X =
      sequentialOrthogonalAdjunction.unit.app (sequentialOriginalQ.obj X) ≫
        sequentialOrthogonalRestriction.map
          (orthogonalOriginalRUnit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X))) := rfl

/-- Every symmetric source keeps the complete original Q/unit/restricted-K composite. -/
theorem symmetricDerivedUnit_app (X : YC.{u, v}) :
    symmetricDerivedUnit.app X =
      symmetricOrthogonalAdjunction.unit.app (symmetricOriginalQ.obj X) ≫
        symmetricOrthogonalRestriction.map
          (orthogonalOriginalRUnit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X))) := rfl

/-- All original orthogonal targets retain the full sequential Q-counit/coend-counit composite. -/
theorem sequentialDerivedCounit_app (E : OC.{u, v}) :
    sequentialDerivedCounit.app E =
      sequentialOrthogonalLan.map (sequentialOriginalQCounit.app
        (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj E))) ≫
          sequentialOrthogonalAdjunction.counit.app (orthogonalOriginalR.obj E) := rfl

/-- The actual symmetric derived counit retains both whole original counit maps. -/
theorem symmetricDerivedCounit_app (E : OC.{u, v}) :
    symmetricDerivedCounit.app E =
      symmetricOrthogonalLan.map (symmetricOriginalQCounit.app
        (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj E))) ≫
          symmetricOrthogonalAdjunction.counit.app (orthogonalOriginalR.obj E) := rfl

/-- The entire sequential derived counit is the original inverse adjunct
of the actual source I counit at the original target K replacement. -/
theorem sequentialDerivedCounit_homEquiv (E : OC.{u, v}) :
    sequentialOrthogonalAdjunction.homEquiv
        (sequentialOriginalQ.obj (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj E)))
        (orthogonalOriginalR.obj E) (sequentialDerivedCounit.app E) =
      sequentialOriginalQCounit.app (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj E)) := by
  have h := sequentialOrthogonalAdjunction.homEquiv_counit
    (g := sequentialOriginalQCounit.app (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj E)))
  rw [sequentialDerivedCounit_app, ← h,
    Equiv.apply_symm_apply]

/-- The complete symmetric derived counit retains the unchanged inverse Hom function. -/
theorem symmetricDerivedCounit_homEquiv (E : OC.{u, v}) :
    symmetricOrthogonalAdjunction.homEquiv
        (symmetricOriginalQ.obj (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj E)))
        (orthogonalOriginalR.obj E) (symmetricDerivedCounit.app E) =
      symmetricOriginalQCounit.app (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj E)) := by
  have h := symmetricOrthogonalAdjunction.homEquiv_counit
    (g := symmetricOriginalQCounit.app (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj E)))
  rw [symmetricDerivedCounit_app, ← h,
    Equiv.apply_symm_apply]

/-- The first sequential replacement triangle is the actual original
Lan-Q counit followed by the complete original orthogonal K unit. -/
theorem sequentialDerivedTriangle_left (X : SC.{u, v}) :
    sequentialOrthogonalLan.map (sequentialOriginalQ.map (sequentialDerivedUnit.app X)) ≫
        sequentialDerivedCounit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X)) =
      sequentialOrthogonalLan.map (sequentialOriginalQCounit.app (sequentialOriginalQ.obj X)) ≫
        orthogonalOriginalRUnit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X)) := by
  have hQ := sequentialOriginalQCounit.naturality (sequentialDerivedUnit.app X)
  have hCounit := sequentialOrthogonalAdjunction.counit.naturality
    (orthogonalOriginalRUnit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X)))
  have hTriangle := sequentialOrthogonalAdjunction.left_triangle_components (sequentialOriginalQ.obj X)
  have hId : 𝟙 (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X)) ≫
        orthogonalOriginalRUnit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X)) =
      orthogonalOriginalRUnit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X)) := by
    simpa only [Functor.id_obj] using Category.id_comp
      (orthogonalOriginalRUnit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X)))
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hQ hCounit
  rw [sequentialDerivedCounit_app, ← Category.assoc, ← sequentialOrthogonalLan.map_comp,
    hQ, sequentialOrthogonalLan.map_comp, Category.assoc, sequentialDerivedUnit_app,
    sequentialOrthogonalLan.map_comp]
  simp only [Category.assoc]
  rw [hCounit,
    ← Category.assoc (sequentialOrthogonalLan.map
      (sequentialOrthogonalAdjunction.unit.app (sequentialOriginalQ.obj X)))
      (sequentialOrthogonalAdjunction.counit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X)))
      (orthogonalOriginalRUnit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X))),
    hTriangle]
  rw [hId]

/-- The first symmetric replacement triangle keeps the same original
coend, Q counit and full target-K inclusion functions. -/
theorem symmetricDerivedTriangle_left (X : YC.{u, v}) :
    symmetricOrthogonalLan.map (symmetricOriginalQ.map (symmetricDerivedUnit.app X)) ≫
        symmetricDerivedCounit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X)) =
      symmetricOrthogonalLan.map (symmetricOriginalQCounit.app (symmetricOriginalQ.obj X)) ≫
        orthogonalOriginalRUnit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X)) := by
  have hQ := symmetricOriginalQCounit.naturality (symmetricDerivedUnit.app X)
  have hCounit := symmetricOrthogonalAdjunction.counit.naturality
    (orthogonalOriginalRUnit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X)))
  have hTriangle := symmetricOrthogonalAdjunction.left_triangle_components (symmetricOriginalQ.obj X)
  have hId : 𝟙 (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X)) ≫
        orthogonalOriginalRUnit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X)) =
      orthogonalOriginalRUnit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X)) := by
    simpa only [Functor.id_obj] using Category.id_comp
      (orthogonalOriginalRUnit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X)))
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hQ hCounit
  rw [symmetricDerivedCounit_app, ← Category.assoc, ← symmetricOrthogonalLan.map_comp,
    hQ, symmetricOrthogonalLan.map_comp, Category.assoc, symmetricDerivedUnit_app,
    symmetricOrthogonalLan.map_comp]
  simp only [Category.assoc]
  rw [hCounit,
    ← Category.assoc (symmetricOrthogonalLan.map
      (symmetricOrthogonalAdjunction.unit.app (symmetricOriginalQ.obj X)))
      (symmetricOrthogonalAdjunction.counit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X)))
      (orthogonalOriginalRUnit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X))),
    hTriangle]
  rw [hId]

/-- The second sequential triangle is the original source Q counit
followed by restriction of the genuine K unit at the original K target. -/
theorem sequentialDerivedTriangle_right (E : OC.{u, v}) :
    sequentialDerivedUnit.app (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj E)) ≫
        sequentialOrthogonalRestriction.map (orthogonalOriginalR.map (sequentialDerivedCounit.app E)) =
      sequentialOriginalQCounit.app (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj E)) ≫
        sequentialOrthogonalRestriction.map (orthogonalOriginalRUnit.app (orthogonalOriginalR.obj E)) := by
  have hAdjunct :
      sequentialOrthogonalAdjunction.unit.app
          (sequentialOriginalQ.obj (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj E))) ≫
        sequentialOrthogonalRestriction.map (sequentialDerivedCounit.app E) =
      sequentialOriginalQCounit.app (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj E)) :=
    (sequentialOrthogonalAdjunction.homEquiv_unit (f := sequentialDerivedCounit.app E)).symm.trans
      (sequentialDerivedCounit_homEquiv E)
  have hR := orthogonalOriginalRUnit.naturality (sequentialDerivedCounit.app E)
  simp only [Functor.id_map, Functor.comp_obj] at hR
  rw [sequentialDerivedUnit_app, Category.assoc, ← sequentialOrthogonalRestriction.map_comp,
    ← hR, sequentialOrthogonalRestriction.map_comp, ← Category.assoc, hAdjunct]

/-- The second symmetric triangle retains both original replacement
maps and the full native restricted target-unit map. -/
theorem symmetricDerivedTriangle_right (E : OC.{u, v}) :
    symmetricDerivedUnit.app (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj E)) ≫
        symmetricOrthogonalRestriction.map (orthogonalOriginalR.map (symmetricDerivedCounit.app E)) =
      symmetricOriginalQCounit.app (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj E)) ≫
        symmetricOrthogonalRestriction.map (orthogonalOriginalRUnit.app (orthogonalOriginalR.obj E)) := by
  have hAdjunct :
      symmetricOrthogonalAdjunction.unit.app
          (symmetricOriginalQ.obj (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj E))) ≫
        symmetricOrthogonalRestriction.map (symmetricDerivedCounit.app E) =
      symmetricOriginalQCounit.app (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj E)) :=
    (symmetricOrthogonalAdjunction.homEquiv_unit (f := symmetricDerivedCounit.app E)).symm.trans
      (symmetricDerivedCounit_homEquiv E)
  have hR := orthogonalOriginalRUnit.naturality (symmetricDerivedCounit.app E)
  simp only [Functor.id_map, Functor.comp_obj] at hR
  rw [symmetricDerivedUnit_app, Category.assoc, ← symmetricOrthogonalRestriction.map_comp,
    ← hR, symmetricOrthogonalRestriction.map_comp, ← Category.assoc, hAdjunct]

/-- Every actual original orthogonal K unit satisfies all original Omega Hom tests. -/
theorem orthogonalOriginalRUnit_omegaTests (E : OC.{u, v}) :
    NativeK.omegaTests orthogonalFamily (orthogonalOriginalRUnit.app E) :=
  PointedCGWH.Spectra.NativeStable.orthogonalKLeft_le_omegaTests _
    (NativeK.omegaReplacementUnit_mem_left orthogonalFamily E)

/-- The original full orthogonal K algorithm has its genuine Omega output at every source. -/
theorem orthogonalOriginalR_isOmega (E : OC.{u, v}) :
    NativeK.IsOmega orthogonalFamily (orthogonalOriginalR.obj E) :=
  NativeK.omegaReplacement_isOmega orthogonalFamily E

/-- At its genuine Omega target the original K unit is an actual level weak map. -/
theorem orthogonalOriginalRUnit_atR_levelWeak (E : OC.{u, v}) :
    weakEquivalences OC (orthogonalOriginalRUnit.app (orthogonalOriginalR.obj E)) := by
  let f : orthogonalOriginalR.obj E ⟶ orthogonalOriginalR.obj (orthogonalOriginalR.obj E) :=
    orthogonalOriginalRUnit.app (orthogonalOriginalR.obj E)
  change weakEquivalences OC f
  have hX := orthogonalOriginalR_isOmega E
  have hY := orthogonalOriginalR_isOmega (orthogonalOriginalR.obj E)
  have hf : NativeK.omegaTests orthogonalFamily f :=
    orthogonalOriginalRUnit_omegaTests (orthogonalOriginalR.obj E)
  exact (NativeK.omegaTests_iff_levelWeak_of_isOmega orthogonalFamily f hX hY).mp hf

/-- The complete original K unit square preserves and reflects all target
Omega Hom tests on arbitrary original arrows. -/
theorem orthogonalOriginalR_map_omegaTests_iff {X Y : OC.{u, v}} (f : X ⟶ Y) :
    NativeK.omegaTests orthogonalFamily (orthogonalOriginalR.map f) ↔
      NativeK.omegaTests orthogonalFamily f := by
  let W := NativeK.omegaTests orthogonalFamily
  have hX : W (orthogonalOriginalRUnit.app X) := orthogonalOriginalRUnit_omegaTests X
  have hY : W (orthogonalOriginalRUnit.app Y) := orthogonalOriginalRUnit_omegaTests Y
  have hn := orthogonalOriginalRUnit.naturality f
  simp only [Functor.id_map] at hn
  constructor
  · intro hf
    have h := W.comp_mem _ _ hX hf
    rw [← hn] at h
    exact W.of_postcomp _ _ hY h
  · intro hf
    have h := W.comp_mem _ _ hf hY
    rw [hn] at h
    exact W.of_precomp _ _ hX h

/-- The sequential right derived functor uses the actual full target K
algorithm followed by the unchanged complete restriction. -/
abbrev sequentialRightDerivedRestriction : OC.{u, v} ⥤ SC.{u, v} :=
  orthogonalOriginalR ⋙ sequentialOrthogonalRestriction

/-- The symmetric right derived functor retains all original target-K
maps and the whole native permutation restriction. -/
abbrev symmetricRightDerivedRestriction : OC.{u, v} ⥤ YC.{u, v} :=
  orthogonalOriginalR ⋙ symmetricOrthogonalRestriction

/-- On every original arrow, the actual sequential right derived
restriction preserves and reflects the entire native weak-test class. -/
theorem sequentialRightDerivedRestriction_omegaTests_iff {X Y : OC.{u, v}} (f : X ⟶ Y) :
    NativeK.omegaTests sSeq (sequentialRightDerivedRestriction.map f) ↔
      NativeK.omegaTests orthogonalFamily f :=
  (sequentialRestriction_omegaTests_iff_of_isOmega (orthogonalOriginalR.map f)
    (orthogonalOriginalR_isOmega X) (orthogonalOriginalR_isOmega Y)).trans
      (orthogonalOriginalR_map_omegaTests_iff f)

/-- The actual symmetric right derived restriction preserves and
reflects the full native weak class. Its inputs are the actual K outputs;
no arbitrary-source raw-pi converse or semistability erasure is used. -/
theorem symmetricRightDerivedRestriction_omegaTests_iff {X Y : OC.{u, v}} (f : X ⟶ Y) :
    NativeK.omegaTests symmetricFamily (symmetricRightDerivedRestriction.map f) ↔
      NativeK.omegaTests orthogonalFamily f :=
  (symmetricRestriction_omegaTests_iff_of_isOmega (orthogonalOriginalR.map f)
    (orthogonalOriginalR_isOmega X) (orthogonalOriginalR_isOmega Y)).trans
      (orthogonalOriginalR_map_omegaTests_iff f)

/-- The original sequential Lan-Q counit at the actual Q object satisfies
all target tests, using the same source I cofibrancy witness. -/
theorem sequentialLanQCounitAtQ_omegaTests (X : SC.{u, v}) :
    NativeK.omegaTests orthogonalFamily
      (sequentialOrthogonalLan.map (sequentialOriginalQCounit.app (sequentialOriginalQ.obj X))) := by
  let _ : IsCofibrant (sequentialOriginalQ.obj X) := originalQ_isCofibrant X
  let _ : IsCofibrant ((𝟭 SC).obj (sequentialOriginalQ.obj X)) := by
    simpa only [Functor.id_obj] using (originalQ_isCofibrant X)
  let _ : IsCofibrant (sequentialOriginalQ.obj (sequentialOriginalQ.obj X)) :=
    originalQ_isCofibrant (sequentialOriginalQ.obj X)
  have hLevel : weakEquivalences OC
      (sequentialOrthogonalLan.map (sequentialOriginalQCounit.app (sequentialOriginalQ.obj X))) :=
    originalLan_levelWeak_of_cofibrant sequentialOrthogonalOperatorIndexFunctor
      (sequentialOriginalQCounit.app (sequentialOriginalQ.obj X))
      (originalQCounit_levelWeak (sequentialOriginalQ.obj X))
  exact NativeK.levelWeak_le_omegaTests orthogonalFamily _ hLevel

/-- The actual symmetric Q source gives the same original Lan-Q counit tests. -/
theorem symmetricLanQCounitAtQ_omegaTests (X : YC.{u, v}) :
    NativeK.omegaTests orthogonalFamily
      (symmetricOrthogonalLan.map (symmetricOriginalQCounit.app (symmetricOriginalQ.obj X))) := by
  let _ : IsCofibrant (symmetricOriginalQ.obj X) := originalQ_isCofibrant X
  let _ : IsCofibrant ((𝟭 YC).obj (symmetricOriginalQ.obj X)) := by
    simpa only [Functor.id_obj] using (originalQ_isCofibrant X)
  let _ : IsCofibrant (symmetricOriginalQ.obj (symmetricOriginalQ.obj X)) :=
    originalQ_isCofibrant (symmetricOriginalQ.obj X)
  have hLevel : weakEquivalences OC
      (symmetricOrthogonalLan.map (symmetricOriginalQCounit.app (symmetricOriginalQ.obj X))) :=
    originalLan_levelWeak_of_cofibrant symmetricOrthogonalOperatorIndexFunctor
      (symmetricOriginalQCounit.app (symmetricOriginalQ.obj X))
      (originalQCounit_levelWeak (symmetricOriginalQ.obj X))
  exact NativeK.levelWeak_le_omegaTests orthogonalFamily _ hLevel

/-- The actual first sequential replacement-triangle composite has every
orthogonal Omega Hom test on every original source. -/
theorem sequentialDerivedTriangle_left_omegaTests (X : SC.{u, v}) :
    NativeK.omegaTests orthogonalFamily
      (sequentialOrthogonalLan.map (sequentialOriginalQ.map (sequentialDerivedUnit.app X)) ≫
        sequentialDerivedCounit.app (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X))) := by
  have h := (NativeK.omegaTests orthogonalFamily).comp_mem _ _
    (sequentialLanQCounitAtQ_omegaTests X)
    (orthogonalOriginalRUnit_omegaTests (sequentialOrthogonalLan.obj (sequentialOriginalQ.obj X)))
  exact (sequentialDerivedTriangle_left X).symm ▸ h

/-- The full first symmetric replacement-triangle composite satisfies
every original orthogonal Omega-target test, with no endpoint restriction. -/
theorem symmetricDerivedTriangle_left_omegaTests (X : YC.{u, v}) :
    NativeK.omegaTests orthogonalFamily
      (symmetricOrthogonalLan.map (symmetricOriginalQ.map (symmetricDerivedUnit.app X)) ≫
        symmetricDerivedCounit.app (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X))) := by
  have h := (NativeK.omegaTests orthogonalFamily).comp_mem _ _
    (symmetricLanQCounitAtQ_omegaTests X)
    (orthogonalOriginalRUnit_omegaTests (symmetricOrthogonalLan.obj (symmetricOriginalQ.obj X)))
  exact (symmetricDerivedTriangle_left X).symm ▸ h

/-- The entire second sequential triangle has the original source Omega
tests by the actual Q counit and restricted level-weak target K unit. -/
theorem sequentialDerivedTriangle_right_omegaTests (E : OC.{u, v}) :
    NativeK.omegaTests sSeq
      (sequentialDerivedUnit.app (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj E)) ≫
        sequentialOrthogonalRestriction.map (orthogonalOriginalR.map (sequentialDerivedCounit.app E))) := by
  rw [sequentialDerivedTriangle_right E]
  exact (NativeK.omegaTests sSeq).comp_mem _ _
    (NativeK.levelWeak_le_omegaTests sSeq _
      (originalQCounit_levelWeak (sequentialOrthogonalRestriction.obj (orthogonalOriginalR.obj E))))
    (NativeK.levelWeak_le_omegaTests sSeq _
      ((sequentialRestriction_levelWeak_iff _).mpr (orthogonalOriginalRUnit_atR_levelWeak E)))

/-- The entire second symmetric replacement triangle preserves every
native source test through the unchanged original Q/R functions. -/
theorem symmetricDerivedTriangle_right_omegaTests (E : OC.{u, v}) :
    NativeK.omegaTests symmetricFamily
      (symmetricDerivedUnit.app (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj E)) ≫
        symmetricOrthogonalRestriction.map (orthogonalOriginalR.map (symmetricDerivedCounit.app E))) := by
  rw [symmetricDerivedTriangle_right E]
  exact (NativeK.omegaTests symmetricFamily).comp_mem _ _
    (NativeK.levelWeak_le_omegaTests symmetricFamily _
      (originalQCounit_levelWeak (symmetricOrthogonalRestriction.obj (orthogonalOriginalR.obj E))))
    (NativeK.levelWeak_le_omegaTests symmetricFamily _
      ((symmetricRestriction_levelWeak_iff _).mpr (orthogonalOriginalRUnit_atR_levelWeak E)))

end PointedCGWH.Spectra.Orthogonal.IndexKan.NativeStableIndexComparisons
