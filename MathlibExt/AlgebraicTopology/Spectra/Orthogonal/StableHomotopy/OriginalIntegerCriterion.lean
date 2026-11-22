/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaIntegerIsomorphism
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.OriginalIntegerCharacterization

/-!
# Unrestricted integer criterion for original orthogonal spectra

The original Omega-target tests of every arrow are equivalent to isomorphisms
on all signed integer homotopy groups. The actual I counit, paired K unit,
complete replacement comparisons and both endpoint squares are retained.

The result holds for every caller choice of the realized-generator bottom.
The canonical instance is exposed in `OriginalCanonicalIntegerCriterion`.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.Spectra.Orthogonal.OriginalIntegerCharacterization
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.OriginalIntegerCriterionComplete

/-- The actual original paired K stabilization maps have every signed integer
test, derived from the proved zero-to-n native sphere maps. -/
theorem original_stabilizations_integerPiStar (l : ℕ × ℕ) :
    integerPiStarEquivalences
      (NativeK.stabilization Actual.orthogonalFamily.{u, v} l) := by
  apply BareGammaSeedClosure.originalStabilizations_integerPiStar_of_bareGammaSeeds ?_ l
  intro n
  apply (integerPiStarEquivalences_iff _).mpr
  intro q
  exact NativeGammaFaceBridge.native_stabilization_integer_isIso.{u, v} n q

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The entire actual K-unit group family, with no seed or converse premise. -/
def originalKUnitIntegerNatIso (q : ℤ) :
    integerPiFunctor.{u, v} q ≅
      NativeStableModels.fibrantReplacement (B := B) ⋙ integerPiFunctor q :=
  originalKUnitIntegerNatIsoOfStabilizationSeeds (B := B)
    (fun l => original_stabilizations_integerPiStar l) q

/-- The actual K unit has every original integer test for arbitrary endpoints. -/
theorem originalKUnit_integerPiStar (X : Actual.OrthogonalCarrier.{u, v}) :
    integerPiStarEquivalences ((NativeStableModels.rUnit (B := B)).app X) :=
  originalKUnit_integerPiStar_of_stabilizationSeeds (B := B)
    (fun l => original_stabilizations_integerPiStar l) X

/-- Both complete original replacement endpoint families are isomorphic through
the inverse I counit followed by the actual K unit. -/
def originalIntegerReplacementComparisonIso (q : ℤ) :
    integerPiFunctor.{u, v} q ≅
      (NativeStableModels.cofibrantReplacement (B := B) ⋙
        NativeStableModels.fibrantReplacement (B := B)) ⋙ integerPiFunctor q :=
  integerReplacementComparisonIsoOfStabilizationSeeds (B := B)
    (fun l => original_stabilizations_integerPiStar l) q

/-- The forward comparison keeps the literal original I inverse and K-unit map. -/
theorem originalIntegerReplacementComparisonIso_hom_app (q : ℤ)
    (X : Actual.OrthogonalCarrier.{u, v}) :
    (originalIntegerReplacementComparisonIso (B := B) q).hom.app X =
      (NativeStableCofiberIntegerMaps.qCounitIntegerNatIso (B := B)
        (j := CategoryTheory.Spectra.SpectrumIndexMaps.sequentialOrthogonalOperatorIndexFunctor.{u, v})
        q).inv.app X ≫
      (integerPiFunctor q).map ((NativeStableModels.rUnit (B := B)).app
        ((NativeStableModels.cofibrantReplacement (B := B)).obj X)) := rfl

/-- The inverse comparison keeps the actual inverse K unit and original I counit. -/
theorem originalIntegerReplacementComparisonIso_inv_app (q : ℤ)
    (X : Actual.OrthogonalCarrier.{u, v}) :
    (originalIntegerReplacementComparisonIso (B := B) q).inv.app X =
      (originalKUnitIntegerNatIso (B := B) q).inv.app
        ((NativeStableModels.cofibrantReplacement (B := B)).obj X) ≫
      (integerPiFunctor q).map ((NativeStableModels.qCounit (B := B)).app X) := rfl

/-- The full original arbitrary-arrow integer square has both whole endpoints. -/
def originalIntegerReplacementArrowIso (q : ℤ)
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    Arrow.mk ((integerPiFunctor q).map f) ≅
      Arrow.mk ((integerPiFunctor q).map
        ((NativeStableModels.fibrantReplacement (B := B)).map
          ((NativeStableModels.cofibrantReplacement (B := B)).map f))) := by
  let e := originalIntegerReplacementComparisonIso (B := B) q
  exact Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm

/-- Each unchanged integer degree transfers in both directions through the
actual I approximation and paired K target square. -/
theorem originalRQMap_integer_isIso_iff (q : ℤ)
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    IsIso ((integerPiFunctor q).map
        ((NativeStableModels.fibrantReplacement (B := B)).map
          ((NativeStableModels.cofibrantReplacement (B := B)).map f))) ↔
      IsIso ((integerPiFunctor q).map f) :=
  (MorphismProperty.isomorphisms GrpCat.{v}).arrow_mk_iso_iff
    (originalIntegerReplacementArrowIso (B := B) q f).symm

/-- The unrestricted original orthogonal criterion: arbitrary endpoints,
all original Omega-target level-Ho tests, and every signed integer map. -/
theorem originalOmegaTests_iff_integerPiIsos
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v} f ↔
      ∀ q : ℤ, IsIso ((integerPiFunctor q).map f) := by
  calc
    NativeK.omegaTests (B := B) Actual.orthogonalFamily f ↔
        integerPiStarEquivalences
          ((NativeStableModels.fibrantReplacement (B := B)).map
            ((NativeStableModels.cofibrantReplacement (B := B)).map f)) :=
      (rqMap_integerPiStar_iff_omegaTests (B := B) f).symm
    _ ↔ ∀ q : ℤ, IsIso ((integerPiFunctor q).map f) := by
      rw [integerPiStarEquivalences_iff]
      exact forall_congr' (fun q => originalRQMap_integer_isIso_iff (B := B) q f)

/-- The same unrestricted criterion as an equality of the original weak tests. -/
theorem originalOmegaTests_iff_integerPiStar
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v} f ↔
      integerPiStarEquivalences f :=
  (originalOmegaTests_iff_integerPiIsos (B := B) f).trans
    (integerPiStarEquivalences_iff f).symm

end PointedCGWH.Spectra.Orthogonal.OriginalIntegerCriterionComplete
