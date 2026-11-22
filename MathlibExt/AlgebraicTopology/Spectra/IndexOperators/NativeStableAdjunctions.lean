/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.NativeStableIndexComparisons
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOrthogonalStableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeSymmetricStableModelConstruction
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialIndexStabilizationArrowTransport

/-!
# The three original native stable index adjunctions

The complete original N/I, Sigma/I and N/Sigma weighted-coend/restriction
adjunctions are Quillen for the already constructed native stable models on
the unchanged enriched functor carriers. Their original I/K generator images
and actual lifting-class identities supply both preservation obligations.
The original units, counits and all morphism functions are the same adjunction
records. The parameter universes and caller generator-cardinal bottom remain
arbitrary throughout.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC uD vD

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential
open PointedCGWH.Spectra.NativeIndexKanComposition
open PointedCGWH.Spectra.Orthogonal.IndexKan
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

namespace PointedCGWH.Spectra.NativeStableIndexAdjunctions
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private instance basedLimits : HasLimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  change HasLimitsOfSize.{v, v} (Under CGWH.point.{u, v})
  infer_instance

private instance basedProducts : ∀ (J : Type v), HasLimitsOfShape (Discrete J) PointedCGWH.{u, v} :=
  fun _ => by infer_instance

section OriginalLevel
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

omit B in
private theorem original_levelI_images
    {A D : Type} [EnrichedCategory PointedCGWH.{u, v} A] [EnrichedCategory PointedCGWH.{u, v} D]
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) (hf : NativeK.levelI f) :
    (NativeK.levelI (I := D)).rlp.llp ((leftKan j).map f) := by
  have hm : leftKanImage j (NativeK.levelI (I := A)) ((leftKan j).map f) :=
    MorphismProperty.map_mem_map _ _ f hf
  have hi : (NativeK.levelI (I := D)).isoClosure ((leftKan j).map f) :=
    leftKan_generators_le j PointedCGWH.realizedBoundaryInclusions _ hm
  exact ((MorphismProperty.isoClosure_le_iff _ _).mpr
    (NativeK.levelI (I := D)).le_llp_rlp) _ hi

omit B in
private theorem original_K_images
    {A D : Type} [EnrichedCategory PointedCGWH.{u, v} A] [EnrichedCategory PointedCGWH.{u, v} D]
    {L M : Type} (s : NativeStabilizationFamily.{u, v} A L)
    (t : NativeStabilizationFamily.{u, v} D M)
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    (hImage : (NativeK.generators s).map (leftKan j) ≤ (NativeK.generators t).isoClosure)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (hf : NativeK.generators s f) :
    (NativeK.generators t).rlp.llp ((leftKan j).map f) := by
  have hi := hImage _ (MorphismProperty.map_mem_map _ _ _ hf)
  exact ((MorphismProperty.isoClosure_le_iff _ _).mpr
    (NativeK.generators t).le_llp_rlp) _ hi

end OriginalLevel

omit B in
private theorem restriction_rlp_of_images
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (G : MorphismProperty C) (H : MorphismProperty D)
    (hImage : ∀ {X Y : C} (f : X ⟶ Y), G f → H.rlp.llp (L.map f))
    {X Y : D} (p : X ⟶ Y) (hp : H.rlp p) : G.rlp (R.map p) := by
  intro A Z f hf
  exact (a.hasLiftingProperty_iff f p).mp ((hImage f hf) p hp)

section Stable

attribute [local instance] StableModelConstruction.sequentialModelCategory
  StableModelConstruction.symmetricModelCategory StableModelConstruction.orthogonalModelCategory

/-- The actual stable N/I pair preserves both full original I/K right classes.
Every original generator image, actual coend and complete restriction is retained. -/
theorem sequentialOrthogonal_stable_isQuillen :
    sequentialOrthogonalAdjunction.{u, v}.IsQuillenAdjunction := by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations (adj := sequentialOrthogonalAdjunction)
  · intro X Y p hp
    rw [StableModelConstruction.orthogonal_five_classes.2.2.1] at hp
    rw [StableModelConstruction.sequential_five_classes.2.2.1]
    apply restriction_rlp_of_images sequentialOrthogonalAdjunction
      (NativeK.generators PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family)
      (NativeK.generators orthogonalFamily) ?_ p hp
    intro A Z f hf
    apply original_K_images PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family
      orthogonalFamily sequentialOrthogonalOperatorIndexFunctor ?_ f hf
    simpa only [PointedCGWH.SequentialSpectrum.StabilizationKAdapter.generators_eq] using
      sequentialOrthogonal_K_image_le.{u, v}
  · intro X Y p hp
    rw [StableModelConstruction.orthogonal_five_classes.2.2.2.2] at hp
    rw [StableModelConstruction.sequential_five_classes.2.2.2.2]
    exact restriction_rlp_of_images sequentialOrthogonalAdjunction NativeK.levelI NativeK.levelI
      (original_levelI_images sequentialOrthogonalOperatorIndexFunctor) p hp

/-- The actual Sigma/I Quillen adjunction uses the entire original finite-block K images
and both genuine lifting-class identities of the constructed stable models. -/
theorem symmetricOrthogonal_stable_isQuillen :
    symmetricOrthogonalAdjunction.{u, v}.IsQuillenAdjunction := by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations (adj := symmetricOrthogonalAdjunction)
  · intro X Y p hp
    rw [StableModelConstruction.orthogonal_five_classes.2.2.1] at hp
    rw [StableModelConstruction.symmetric_five_classes.2.2.1]
    apply restriction_rlp_of_images symmetricOrthogonalAdjunction
      (NativeK.generators symmetricFamily) (NativeK.generators orthogonalFamily) ?_ p hp
    intro A Z f hf
    apply original_K_images symmetricFamily orthogonalFamily symmetricOrthogonalOperatorIndexFunctor
      symmetricOrthogonal_K_image.{u, v}.le f hf
  · intro X Y p hp
    rw [StableModelConstruction.orthogonal_five_classes.2.2.2.2] at hp
    rw [StableModelConstruction.symmetric_five_classes.2.2.2.2]
    exact restriction_rlp_of_images symmetricOrthogonalAdjunction NativeK.levelI NativeK.levelI
      (original_levelI_images symmetricOrthogonalOperatorIndexFunctor) p hp

/-- The original topological N/Sigma Quillen pair retains the one-circle source,
the complete target permutation and every original cylinder/boundary/horn label. -/
theorem sequentialSymmetric_stable_isQuillen :
    sequentialSymmetricAdjunction.{u, v}.IsQuillenAdjunction := by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations (adj := sequentialSymmetricAdjunction)
  · intro X Y p hp
    rw [StableModelConstruction.symmetric_five_classes.2.2.1] at hp
    rw [StableModelConstruction.sequential_five_classes.2.2.1]
    apply restriction_rlp_of_images sequentialSymmetricAdjunction
      (NativeK.generators PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family)
      (NativeK.generators symmetricFamily) ?_ p hp
    intro A Z f hf
    apply original_K_images PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family
      symmetricFamily sequentialSymmetricOperatorIndexFunctor ?_ f hf
    simpa only [PointedCGWH.SequentialSpectrum.StabilizationKAdapter.generators_eq] using
      sequentialSymmetric_K_image_le.{u, v}
  · intro X Y p hp
    rw [StableModelConstruction.symmetric_five_classes.2.2.2.2] at hp
    rw [StableModelConstruction.sequential_five_classes.2.2.2.2]
    exact restriction_rlp_of_images sequentialSymmetricAdjunction NativeK.levelI NativeK.levelI
      (original_levelI_images sequentialSymmetricOperatorIndexFunctor) p hp


end Stable
end PointedCGWH.Spectra.NativeStableIndexAdjunctions
