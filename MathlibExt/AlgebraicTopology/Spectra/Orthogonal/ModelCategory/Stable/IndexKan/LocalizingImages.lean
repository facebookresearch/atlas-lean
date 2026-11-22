/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.OmegaHomTestTransport
import MathlibExt.CategoryTheory.Enriched.FreeStabilizationKan
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.IndexStabilizationArrowTransport
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.OriginalFreeMaps
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.StabilizationSourceTests
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.DerivedLocalMapping

/-!
# Actual original stabilization-map images of native orthogonal Lan

Every original stabilization arrow satisfies the full original
Omega-target tests, by its actual mapping-end transpose. The original
free source and target are cofibrant by the given coefficient's proved
native cofibrancy. The existing original adjunction and Omega restriction
therefore show that its unchanged raw Lan image satisfies all orthogonal
tests and the matching derived local-equivalence class.

Every label retains its source, target, coefficient and full original
inclusion in the Arrow function and its actual free comparison. The
complete symmetric pair also retains the original sphere comparison
and gives an Arrow isomorphism to the original orthogonal pair.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
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

variable {A L : Type} [EnrichedCategory PointedCGWH.{u, v} A]

private abbrev AC := EnrichedFunctorCat PointedCGWH.{u, v} A

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

/-- The full original Lan Q image of every original label retains all target Omega tests. -/
theorem prolongedQ_stabilization_omegaTests
    (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (hOmega : ∀ E : OC.{u, v}, NativeK.IsOmega orthogonalFamily E →
      NativeK.IsOmega s ((EnrichedFunctorCat.restriction j).obj E)) (l : L) :
    NativeK.omegaTests orthogonalFamily
      ((prolongedQ (B := B) j).map (NativeK.stabilization s l)) :=
  prolongedQ_omegaTests_of_omegaTests s j hOmega (NativeK.stabilization s l)
    (originalStabilization_omegaTests s l)

/-- The actual raw original Lan image of every original stabilization passes all
orthogonal tests, using both original free cofibrant endpoints. -/
theorem originalLan_stabilization_omegaTests
    (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (hOmega : ∀ E : OC.{u, v}, NativeK.IsOmega orthogonalFamily E →
      NativeK.IsOmega s ((EnrichedFunctorCat.restriction j).obj E)) (l : L) :
    NativeK.omegaTests orthogonalFamily ((originalLan j).map (NativeK.stabilization s l)) := by
  let _ : IsCofibrant (Free.object (s.target l) (s.coefficient l)) :=
    NativeK.stabilization_source_cofibrant s l
  let _ : IsCofibrant (Free.object (s.source l) (𝟙_ PointedCGWH.{u, v})) :=
    NativeK.stabilization_target_cofibrant s l
  exact originalLan_omegaTests_of_omegaTests s j hOmega (NativeK.stabilization s l)
    (originalStabilization_omegaTests s l)

/-- The complete original raw Lan Arrow function retains every original family label. -/
def prolongedStabilizationArrows (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (l : L) : Arrow OC.{u, v} :=
  Arrow.mk ((originalLan j).map (NativeK.stabilization s l))

omit B in
/-- The source is the genuine original coend on the same original target free coefficient. -/
theorem prolongedStabilizationArrows_left (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (l : L) :
    (prolongedStabilizationArrows s j l).left =
      (originalLan j).obj (Free.object (s.target l) (s.coefficient l)) := rfl

omit B in
/-- The target is the original raw coend on the same source-index unit free object. -/
theorem prolongedStabilizationArrows_right (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (l : L) :
    (prolongedStabilizationArrows s j l).right =
      (originalLan j).obj (Free.object (s.source l) (𝟙_ PointedCGWH.{u, v})) := rfl

omit B in
/-- The entire original Arrow hom is the unchanged raw Lan of the actual full source arrow. -/
theorem prolongedStabilizationArrows_hom (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (l : L) :
    (prolongedStabilizationArrows s j l).hom =
      (originalLan j).map (NativeK.stabilization s l) := rfl

/-- Every label of the complete raw prolonged family satisfies all original orthogonal tests. -/
theorem prolongedStabilizationArrows_omegaTests
    (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (hOmega : ∀ E : OC.{u, v}, NativeK.IsOmega orthogonalFamily E →
      NativeK.IsOmega s ((EnrichedFunctorCat.restriction j).obj E)) (l : L) :
    NativeK.omegaTests orthogonalFamily (prolongedStabilizationArrows s j l).hom :=
  originalLan_stabilization_omegaTests s j hOmega l

/-- Each actual raw image lies in the matching native derived local-equivalence class,
with the original full orthogonal localization Arrow function retained. -/
theorem prolongedStabilizationArrows_localEquivalence
    (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (hOmega : ∀ E : OC.{u, v}, NativeK.IsOmega orthogonalFamily E →
      NativeK.IsOmega s ((EnrichedFunctorCat.restriction j).obj E)) (l : L) :
    localEquivalences (DerivedLocalMapping.stabilizationArrows orthogonalFamily)
      (prolongedStabilizationArrows s j l).hom := by
  rw [DerivedLocalMapping.localEquivalences_eq_omegaTests]
  exact prolongedStabilizationArrows_omegaTests s j hOmega l

omit B in
/-- Both actual native free comparisons identify every full prolonged source inclusion. -/
def prolongedStabilizationArrowIso (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (l : L) :
    prolongedStabilizationArrows s j l ≅ Arrow.mk
      (CurrentFree.stabilization (j.obj (s.source l)) (j.obj (s.target l))
        (s.coefficient l) (s.inclusion l ≫ j.map (s.source l) (s.target l))) :=
  eqToIso (congrArg
    (fun F : AC.{u, v} (A := A) ⥤ OC.{u, v} => Arrow.mk (F.map (NativeK.stabilization s l)))
    (originalLan_eq j)) ≪≫
      originalStabilizationArrowIso j (s.source l) (s.target l) (s.coefficient l) (s.inclusion l)

omit B in
/-- The original full coefficient isomorphism supplies both actual Arrow comparison directions. -/
def originalStabilizationCoefficientArrowIso (a b : A) {K T : PointedCGWH.{u, v}}
    (e : K ≅ T) (D : T ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    Arrow.mk (CurrentFree.stabilization a b K (e.hom ≫ D)) ≅
      Arrow.mk (CurrentFree.stabilization a b T D) :=
  Arrow.isoMk ((Free.functor (V := PointedCGWH.{u, v}) b).mapIso e) (Iso.refl _)
    ((CurrentFree.stabilization_coefficient a b e.hom D).trans (Category.comp_id _).symm)

/-- The actual sequential source localization arrow has its original native orthogonal image. -/
theorem sequentialLan_stabilization_omegaTests (n : ℕ) :
    NativeK.omegaTests orthogonalFamily
      ((originalLan sequentialOrthogonalOperatorIndexFunctor).map
        (NativeK.stabilization PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily n)) :=
  originalLan_stabilization_omegaTests PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily
    sequentialOrthogonalOperatorIndexFunctor
    (fun E hE => (sequentialRestriction_isOmega_iff E).mpr hE) n

/-- Every actual pair of symmetric source labels retains its same original raw orthogonal image. -/
theorem symmetricLan_stabilization_omegaTests
    (n a : CategoryTheory.Operad.SmallFinBijGroupoid) :
    NativeK.omegaTests orthogonalFamily
      ((originalLan symmetricOrthogonalOperatorIndexFunctor).map
        (NativeK.stabilization symmetricFamily (n, a))) :=
  originalLan_stabilization_omegaTests symmetricFamily symmetricOrthogonalOperatorIndexFunctor
    (fun E hE => (symmetricRestriction_isOmega_iff E).mpr hE) (n, a)

/-- Every original sequential label maps into the same complete orthogonal
local-equivalence class. -/
theorem sequentialLan_stabilization_localEquivalence (n : ℕ) :
    localEquivalences (DerivedLocalMapping.stabilizationArrows orthogonalFamily)
      ((originalLan sequentialOrthogonalOperatorIndexFunctor).map
        (NativeK.stabilization PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily n)) := by
  rw [DerivedLocalMapping.localEquivalences_eq_omegaTests (B := B) orthogonalFamily]
  exact sequentialLan_stabilization_omegaTests (B := B) n

/-- Both symmetric source labels map into the entire same original orthogonal derived weak class. -/
theorem symmetricLan_stabilization_localEquivalence
    (n a : CategoryTheory.Operad.SmallFinBijGroupoid) :
    localEquivalences (DerivedLocalMapping.stabilizationArrows orthogonalFamily)
      ((originalLan symmetricOrthogonalOperatorIndexFunctor).map
        (NativeK.stabilization symmetricFamily (n, a))) := by
  rw [DerivedLocalMapping.localEquivalences_eq_omegaTests (B := B) orthogonalFamily]
  exact symmetricLan_stabilization_omegaTests (B := B) n a

omit B in
/-- Every complete symmetric pair keeps its actual original sphere comparison and gives the
actual Arrow isomorphism to the original orthogonal pair, including both empty blocks. -/
def symmetricProlongedStabilizationArrowIso
    (n a : CategoryTheory.Operad.SmallFinBijGroupoid) :
    prolongedStabilizationArrows symmetricFamily symmetricOrthogonalOperatorIndexFunctor (n, a) ≅
      Arrow.mk (NativeK.stabilization orthogonalFamily (n.of.len, a.of.len)) :=
  eqToIso (congrArg
    (fun F : Actual.SymmetricCarrier.{u, v} ⥤ Actual.OrthogonalCarrier.{u, v} =>
      Arrow.mk (F.map (NativeK.stabilization symmetricFamily (n, a))))
    (originalLan_eq symmetricOrthogonalOperatorIndexFunctor)) ≪≫
      symmetricOrthogonalStabilizationIso n a

end PointedCGWH.Spectra.Orthogonal.IndexKan
