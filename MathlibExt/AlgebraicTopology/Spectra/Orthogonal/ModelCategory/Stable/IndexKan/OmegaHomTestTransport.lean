/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.KanReplacement

/-!
# Original native Lan maps and all orthogonal Omega Hom tests

The complete original adjoint Hom functions identify each target test of
the original Lan Q map with precomposition by the unchanged source map
into the actual restricted target. This holds for every source arrow,
without cofibrancy or Omega conditions on either endpoint.

The proved full-family Omega restriction laws specialize this identity
to the actual sequential and symmetric index maps. For genuinely
cofibrant original endpoints, the original Lan of the original Q
counit transfers those tests to the raw original coend Lan map.
The full native stable model and source comparison remain separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.IndexKan

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open CategoryTheory.Spectra CategoryTheory.Spectra.SpectrumIndexMaps

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev OC := OrthogonalCarrier.{u, v}

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

private abbrev AC := EnrichedFunctorCat PointedCGWH.{u, v} A

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev HA := toHomotopyCategory (AC.{u, v} (A := A))
private abbrev HO := toHomotopyCategory OC.{u, v}

/-- Each full original Lan Q target test is exactly the test of the original source map
into the actual whole restricted target. -/
theorem prolongedQ_test_bijective_iff
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : AC.{u, v} (A := A)} (f : X ⟶ Y) (E : OC.{u, v}) :
    Function.Bijective
        (fun g : HO.obj ((prolongedQ (B := B) j).obj Y) ⟶ HO.obj E =>
          HO.map ((prolongedQ (B := B) j).map f) ≫ g) ↔
      Function.Bijective
        (fun g : HA.obj Y ⟶ HA.obj ((EnrichedFunctorCat.restriction j).obj E) =>
          HA.map f ≫ g) := by
  let eX := originalHomEquiv (B := B) j X E
  let eY := originalHomEquiv (B := B) j Y E
  let t : (HO.obj ((prolongedQ (B := B) j).obj Y) ⟶ HO.obj E) →
      (HO.obj ((prolongedQ (B := B) j).obj X) ⟶ HO.obj E) :=
    fun g => HO.map ((prolongedQ (B := B) j).map f) ≫ g
  let r : (HA.obj Y ⟶ HA.obj ((EnrichedFunctorCat.restriction j).obj E)) →
      (HA.obj X ⟶ HA.obj ((EnrichedFunctorCat.restriction j).obj E)) :=
    fun g => HA.map f ≫ g
  have hn (g : HO.obj ((prolongedQ (B := B) j).obj Y) ⟶ HO.obj E) :
      eX (t g) = r (eY g) := originalHomEquiv_source j f E g
  constructor
  · intro ht
    let e := eY.symm.trans ((Equiv.ofBijective t ht).trans eX)
    have he : (fun g => e g) = r := by
      funext g
      exact (hn (eY.symm g)).trans
        (congrArg r (eY.apply_symm_apply g))
    have hb : Function.Bijective (fun g => e g) := e.bijective
    rw [he] at hb
    exact hb
  · intro hr
    let e := eY.trans ((Equiv.ofBijective r hr).trans eX.symm)
    have he : (fun g => e g) = t := by
      funext g
      apply eX.injective
      change eX (eX.symm (r (eY g))) = eX (t g)
      exact (eX.apply_symm_apply (r (eY g))).trans (hn g).symm
    have hb : Function.Bijective (fun g => e g) := e.bijective
    rw [he] at hb
    exact hb

/-- All full original orthogonal Omega tests retain the complete restricted target family. -/
theorem prolongedQ_omegaTests_iff_restrictedTests
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : AC.{u, v} (A := A)} (f : X ⟶ Y) :
    NativeK.omegaTests orthogonalFamily ((prolongedQ (B := B) j).map f) ↔
      ∀ E : OC.{u, v}, NativeK.IsOmega orthogonalFamily E →
        Function.Bijective
          (fun g : HA.obj Y ⟶ HA.obj ((EnrichedFunctorCat.restriction j).obj E) =>
            HA.map f ≫ g) := by
  constructor
  · intro hf E hE
    exact (prolongedQ_test_bijective_iff j f E).mp (hf E hE)
  · intro hf E hE
    exact (prolongedQ_test_bijective_iff j f E).mpr (hf E hE)

/-- Actual Omega restriction transfers every source-family test to the original Lan Q map. -/
theorem prolongedQ_omegaTests_of_omegaTests
    {L : Type} (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (hOmega : ∀ E : OC.{u, v}, NativeK.IsOmega orthogonalFamily E →
      NativeK.IsOmega s ((EnrichedFunctorCat.restriction j).obj E))
    {X Y : AC.{u, v} (A := A)} (f : X ⟶ Y) (hf : NativeK.omegaTests s f) :
    NativeK.omegaTests orthogonalFamily ((prolongedQ (B := B) j).map f) := by
  apply (prolongedQ_omegaTests_iff_restrictedTests j f).mpr
  intro E hE
  exact hf ((EnrichedFunctorCat.restriction j).obj E) (hOmega E hE)

/-- For both genuinely cofibrant original endpoints, the original Lan Q counit square
preserves and reflects every full original orthogonal Omega-target test. -/
theorem originalLanQ_map_omegaTests_iff
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : AC.{u, v} (A := A)} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    NativeK.omegaTests orthogonalFamily ((prolongedQ (B := B) j).map f) ↔
      NativeK.omegaTests orthogonalFamily ((originalLan j).map f) := by
  let W := NativeK.omegaTests (B := B) orthogonalFamily
  have hX : W ((originalLanQCounit j).app X) := originalLanQCounit_omegaTests j X
  have hY : W ((originalLanQCounit j).app Y) := originalLanQCounit_omegaTests j Y
  have hn := originalLanQCounit_naturality j f
  constructor
  · intro hf
    have h := W.comp_mem _ _ hf hY
    rw [hn] at h
    exact W.of_precomp _ _ hX h
  · intro hf
    have h := W.comp_mem _ _ hX hf
    rw [← hn] at h
    exact W.of_postcomp _ _ hY h

/-- The unchanged raw original Lan map satisfies every orthogonal Omega test
when its original endpoints are cofibrant and the actual restriction preserves Omega. -/
theorem originalLan_omegaTests_of_omegaTests
    {L : Type} (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (hOmega : ∀ E : OC.{u, v}, NativeK.IsOmega orthogonalFamily E →
      NativeK.IsOmega s ((EnrichedFunctorCat.restriction j).obj E))
    {X Y : AC.{u, v} (A := A)} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (hf : NativeK.omegaTests s f) :
    NativeK.omegaTests orthogonalFamily ((originalLan j).map f) :=
  (originalLanQ_map_omegaTests_iff j f).mp
    (prolongedQ_omegaTests_of_omegaTests s j hOmega f hf)

omit B in
/-- The actual sequential restriction retains the original whole one-circle Omega family. -/
theorem sequentialRestriction_isOmega_iff (E : OC.{u, v}) :
    NativeK.IsOmega PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily
      ((EnrichedFunctorCat.restriction sequentialOrthogonalOperatorIndexFunctor).obj E) ↔
        NativeK.IsOmega orthogonalFamily E :=
  (Sequential.sequential_isOmega_iff _).trans (Sequential.sequentialOrthogonal_isOmega_iff E)

omit B in
/-- Actual permutation-to-orthogonal restriction keeps every pair of native Omega labels. -/
theorem symmetricRestriction_isOmega_iff (E : OC.{u, v}) :
    NativeK.IsOmega symmetricFamily
      ((EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor).obj E) ↔
        NativeK.IsOmega orthogonalFamily E :=
  symmetricOrthogonal_isOmega_iff E

/-- The original sequential index Lan Q map preserves all native Omega tests
on every original source arrow, with arbitrary endpoints. -/
theorem sequentialLanQ_omegaTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily f) :
    NativeK.omegaTests orthogonalFamily
      ((prolongedQ (B := B) sequentialOrthogonalOperatorIndexFunctor).map f) :=
  prolongedQ_omegaTests_of_omegaTests
    PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily
    sequentialOrthogonalOperatorIndexFunctor
    (fun E hE => (sequentialRestriction_isOmega_iff E).mpr hE) f hf

/-- The original symmetric index Lan Q preserves the full native Omega Hom tests
for every native source arrow, without endpoint Omega assumptions. -/
theorem symmetricLanQ_omegaTests {X Y : SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests symmetricFamily f) :
    NativeK.omegaTests orthogonalFamily
      ((prolongedQ (B := B) symmetricOrthogonalOperatorIndexFunctor).map f) :=
  prolongedQ_omegaTests_of_omegaTests symmetricFamily symmetricOrthogonalOperatorIndexFunctor
    (fun E hE => (symmetricRestriction_isOmega_iff E).mpr hE) f hf

/-- The raw original sequential coend Lan preserves all original Omega tests
with both actual original cofibrant endpoints retained. -/
theorem sequentialLan_omegaTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y)
    (hf : NativeK.omegaTests PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily f) :
    NativeK.omegaTests orthogonalFamily
      ((originalLan sequentialOrthogonalOperatorIndexFunctor).map f) :=
  (originalLanQ_map_omegaTests_iff sequentialOrthogonalOperatorIndexFunctor f).mp
    (sequentialLanQ_omegaTests f hf)

/-- The raw original symmetric coend Lan preserves the full original stable test class
on arrows between the actual original cofibrant sources. -/
theorem symmetricLan_omegaTests {X Y : SymmetricCarrier.{u, v}}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) (hf : NativeK.omegaTests symmetricFamily f) :
    NativeK.omegaTests orthogonalFamily
      ((originalLan symmetricOrthogonalOperatorIndexFunctor).map f) :=
  (originalLanQ_map_omegaTests_iff symmetricOrthogonalOperatorIndexFunctor f).mp
    (symmetricLanQ_omegaTests f hf)

namespace NativeStableIndexComparisons

/-- All actual orthogonal dimensions occur in the sequential restriction,
so the whole original level weak class is preserved and reflected. -/
theorem sequentialRestriction_levelWeak_iff {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
      ((EnrichedFunctorCat.restriction sequentialOrthogonalOperatorIndexFunctor).map f) ↔
      weakEquivalences OrthogonalCarrier.{u, v} f :=
  by
    rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq
        (A := PointedCGWH.Spectra.Sequential.Index.{u, v}),
      HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq
        (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}),
      EvaluationTransfer.evaluationProperty_iff, EvaluationTransfer.evaluationProperty_iff]
    change (∀ a : PointedCGWH.Spectra.Sequential.Index.{u, v},
      weakEquivalences PointedCGWH.{u, v}
        (component (restrictionMap sequentialOrthogonalOperatorIndexFunctor f) a)) ↔
      ∀ a : OrthogonalOperatorIndex.{u, v},
        weakEquivalences PointedCGWH.{u, v} (component f a)
    simp only [EnrichedFunctorCat.restrictionMap_component]
    constructor
    · intro h a
      rcases a with ⟨n⟩
      exact h ⟨n⟩
    · intro h a
      exact h (sequentialOrthogonalOperatorIndexFunctor.obj a)

/-- The symmetric restriction detects the original level weak class on arbitrary endpoints. -/
theorem symmetricRestriction_levelWeak_iff {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    weakEquivalences SymmetricCarrier.{u, v}
      ((EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor).map f) ↔
      weakEquivalences OrthogonalCarrier.{u, v} f := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq
      (A := PointedCGWH.SymmetricOperatorIndex.{u, v}),
    HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq
      (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}),
    EvaluationTransfer.evaluationProperty_iff, EvaluationTransfer.evaluationProperty_iff]
  change (∀ a : PointedCGWH.SymmetricOperatorIndex.{u, v},
      weakEquivalences PointedCGWH.{u, v}
        (component (restrictionMap symmetricOrthogonalOperatorIndexFunctor f) a)) ↔
    ∀ a : OrthogonalOperatorIndex.{u, v},
      weakEquivalences PointedCGWH.{u, v} (component f a)
  simp only [EnrichedFunctorCat.restrictionMap_component]
  constructor
  · intro h a
    rcases a with ⟨n⟩
    let a : Operad.SmallFinBijGroupoid := ⟨FintypeCat.Skeleton.mk n⟩
    exact h (PointedCGWH.symmetricOperatorObj a)
  · intro h a
    exact h (symmetricOrthogonalOperatorIndexFunctor.obj a)

/-- The complete original sequential restriction preserves and reflects every
Omega Hom test between actual orthogonal Omega objects. -/
theorem sequentialRestriction_omegaTests_iff_of_isOmega
    {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hX : NativeK.IsOmega orthogonalFamily X) (hY : NativeK.IsOmega orthogonalFamily Y) :
    NativeK.omegaTests PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily
      ((EnrichedFunctorCat.restriction sequentialOrthogonalOperatorIndexFunctor).map f) ↔
      NativeK.omegaTests orthogonalFamily f :=
  (NativeK.omegaTests_iff_levelWeak_of_isOmega PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily
    ((EnrichedFunctorCat.restriction sequentialOrthogonalOperatorIndexFunctor).map f)
    ((sequentialRestriction_isOmega_iff X).mpr hX)
    ((sequentialRestriction_isOmega_iff Y).mpr hY)).trans
      ((sequentialRestriction_levelWeak_iff f).trans
        (NativeK.omegaTests_iff_levelWeak_of_isOmega orthogonalFamily f hX hY).symm)

/-- Full symmetric restriction detects all original tests between orthogonal
Omega objects. The two original endpoint hypotheses remain explicit. -/
theorem symmetricRestriction_omegaTests_iff_of_isOmega
    {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hX : NativeK.IsOmega orthogonalFamily X) (hY : NativeK.IsOmega orthogonalFamily Y) :
    NativeK.omegaTests symmetricFamily
      ((EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor).map f) ↔
      NativeK.omegaTests orthogonalFamily f :=
  (NativeK.omegaTests_iff_levelWeak_of_isOmega symmetricFamily
    ((EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor).map f)
    ((symmetricRestriction_isOmega_iff X).mpr hX)
    ((symmetricRestriction_isOmega_iff Y).mpr hY)).trans
      ((symmetricRestriction_levelWeak_iff f).trans
        (NativeK.omegaTests_iff_levelWeak_of_isOmega orthogonalFamily f hX hY).symm)

end NativeStableIndexComparisons

end PointedCGWH.Spectra.Orthogonal.IndexKan
