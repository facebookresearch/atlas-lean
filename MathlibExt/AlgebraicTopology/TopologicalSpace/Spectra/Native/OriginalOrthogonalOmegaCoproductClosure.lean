/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOrthogonalHEPOmegaCoproductClosure
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderCoproduct
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableCoproductClosure
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderBasedHEP

/-!
# Original orthogonal Omega tests under arbitrary caller coproducts

The original I approximation is retained on every summand. Its original
counit is factored by the actual native mapping cylinder. Genuine HEP
cobase and continuous ordinal closure apply to the complete coordinate
chain of the cylinder source maps. The coproduct cylinder projections
are level weak by the actual same retractions, so the full coproduct of
the original I counits has all Omega tests. The proved cofibrant coproduct
mapping theorem and the entire counit naturality square then give the
original arbitrary-endpoint caller coproduct result.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open PointedCGWH.EnrichedIntervalMappingCylinder
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.OriginalHEPOmegaClosure

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  MonoidalClosed.enrichedCategorySelf PointedCGWH.EnrichedMapping.hasSmallLimits

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev C := Actual.OrthogonalCarrier.{u, v}
private abbrev Q := NativeStableModels.cofibrantReplacement (B := B)
private abbrev ε := NativeStableModels.qCounit (B := B)
private abbrev W := NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v}

/-- The actual original coproduct of I-counits passes every Omega target.
No badly based coproduct level-equivalence assertion is used. -/
theorem originalCoproductCounit_omegaTests {J : Type v} (X : J → C.{u, v}) :
    W (Limits.Sigma.map (fun j => ε.app (X j))) := by
  let f := fun j => Arrow.mk (ε.app (X j))
  let i := fun j => source (f j)
  let r := fun j => retraction (f j)
  have hr (j : J) : W (r j) :=
    NativeK.levelWeak_le_omegaTests Actual.orthogonalFamily _
      ((HomotopicalAlgebra.weakEquivalence_iff _).mp
        (PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.retraction_weakEquivalence (f j)))
  have hi (j : J) : originalHEPOmega (B := B) (i j) := by
    refine ⟨PointedCGWH.EnrichedBasedHomotopyExtension.source_mem (f j), ?_⟩
    have hCounit : W (ε.app (X j)) :=
      NativeK.levelWeak_le_omegaTests Actual.orthogonalFamily _
        (Replacement.cofibrantReplacementCounit_mem_weakEquivalences
          (B := B) (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) (X j))
    have hFac : i j ≫ r j = ε.app (X j) := fac (f j)
    exact W.of_postcomp _ _ (hr j) (hFac.symm ▸ hCounit)
  have hSource : originalHEPOmega (B := B) (Limits.Sigma.map i) :=
    MorphismProperty.coproductMap_mem_of_cobase_transfinite
      (originalHEPOmega (B := B)) i hi
  have hRetraction : W (Limits.Sigma.map r) :=
    NativeK.levelWeak_le_omegaTests Actual.orthogonalFamily _
      (PointedCGWH.EnrichedIntervalMappingCylinder.Coproducts.sigmaRetraction_levelWeak
        (fun j => ε.app (X j)))
  have hFac : Limits.Sigma.map i ≫ Limits.Sigma.map r =
      Limits.Sigma.map (fun j => ε.app (X j)) := by
    apply Sigma.hom_ext
    intro j
    rw [← Category.assoc, Sigma.ι_map, Category.assoc, Sigma.ι_map,
      ← Category.assoc, fac, Sigma.ι_map]
    rfl
  exact hFac ▸ W.comp_mem _ _ hSource.2 hRetraction

/-- The actual arbitrary-endpoint coproduct map passes every original Omega
test, by the original Q-source coproduct theorem and both full counit maps. -/
theorem originalCoproductMap_omegaTests {J : Type v}
    {X Y : J → C.{u, v}} (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, W (f j)) :
    W (Limits.Sigma.map f) := by
  let fq := fun j => Q.map (f j)
  let _ : ∀ j, IsCofibrant (Q.obj (X j)) :=
    fun j => Replacement.isCofibrant_cofibrantReplacement (X j)
  let _ : ∀ j, IsCofibrant (Q.obj (Y j)) :=
    fun j => Replacement.isCofibrant_cofibrantReplacement (Y j)
  have hfq : ∀ j, W (fq j) := fun j =>
    (OriginalIntegerCharacterization.qMap_omegaTests_iff (B := B) (f j)).mpr (hf j)
  have hQ : W (Limits.Sigma.map fq) :=
    StableCoproductClosure.omegaTests_sigmaMap Actual.orthogonalFamily fq hfq
  have hX : W (Limits.Sigma.map (fun j => ε.app (X j))) := originalCoproductCounit_omegaTests X
  have hY : W (Limits.Sigma.map (fun j => ε.app (Y j))) := originalCoproductCounit_omegaTests Y
  have hNat : Limits.Sigma.map fq ≫ Limits.Sigma.map (fun j => ε.app (Y j)) =
      Limits.Sigma.map (fun j => ε.app (X j)) ≫ Limits.Sigma.map f := by
    rw [Sigma.map_comp_map, Sigma.map_comp_map]
    apply congrArg (fun g : ∀ j, Q.obj (X j) ⟶ Y j => Limits.Sigma.map g)
    funext j
    exact ε.naturality (f j)
  exact W.of_precomp _ _ hX (hNat ▸ W.comp_mem _ _ hQ hY)

/-- Both entire original cofan endpoint comparisons retain every caller leg
and the actual caller map. -/
def originalCoproductCallerArrowIso {J : Type v} {X Y : J → C.{u, v}}
    (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j) :
    Arrow.mk (Limits.Sigma.map f) ≅ Arrow.mk p := by
  let eX := (coproductIsCoproduct X).coconePointUniqueUpToIso hc
  let eY := (coproductIsCoproduct Y).coconePointUniqueUpToIso hd
  refine Arrow.isoMk eX eY ?_
  change eX.hom ≫ p = Limits.Sigma.map f ≫ eY.hom
  apply Sigma.hom_ext
  intro j
  have hX : Sigma.ι X j ≫ eX.hom = c.inj j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct X) hc ⟨j⟩
  have hY : Sigma.ι Y j ≫ eY.hom = d.inj j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct Y) hd ⟨j⟩
  rw [← Category.assoc, hX, hp, ← Category.assoc, Sigma.ι_map, Category.assoc, hY]

/-- Every map between actual original colimiting cofans has all Omega tests
from its component maps, with arbitrary endpoints and all injections fixed. -/
theorem originalCofansMap_omegaTests {J : Type v} {X Y : J → C.{u, v}}
    (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j) (hf : ∀ j, W (f j)) : W p :=
  (W.arrow_mk_iso_iff (originalCoproductCallerArrowIso c hc d hd f p hp)).mp
    (originalCoproductMap_omegaTests f hf)

end PointedCGWH.Spectra.Orthogonal.OriginalHEPOmegaClosure
