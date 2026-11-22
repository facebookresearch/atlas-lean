/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSourceStratumWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordZeroLayer

/-!
# Genuine weak comparison on all original normalized word layers

The literal normalization square supplies the SAME full map between the
original layer pushouts. The genuine raw and boundary weak comparisons,
starting with the actual original Hom map in layer zero, imply weakness
on every full finite normalized layer. No layer weakness is an input.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords
variable {O : Type u} {C D : FixedObjects O}

/-- The SAME raw stratum map retains its complete actual normalization square. -/
theorem sourceRawLayerMap_normalize (T : Data C) (F : C ⟶ D) (a b : O) (n : ℕ) :
    rawLayerNormalize T a b n ≫ sourceLayerMap T F a b (n + 1) =
      sourceRawLayerMap T F a b n ≫ rawLayerNormalize (sourceChange T F) a b n := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  apply Subtype.ext
  exact (sourceChange_normalize T F q p.val).symm

/-- The SAME full attaching boundary map retains the previous-layer normalization square. -/
theorem sourceBoundaryLayerMap_normalize (T : Data C) (F : C ⟶ D) (a b : O) (n : ℕ) :
    boundaryLayerNormalize T a b n ≫ sourceLayerMap T F a b n =
      sourceBoundaryLayerMap T F a b n ≫ boundaryLayerNormalize (sourceChange T F) a b n := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  apply Subtype.ext
  exact (sourceChange_normalize T F q p.val).symm

/-- Source change retains the unchanged original raw attaching-boundary inclusion. -/
theorem sourceBoundaryLayerMap_inclusion (T : Data C) (F : C ⟶ D) (a b : O) (n : ℕ) :
    boundaryInclusion T a b n ≫ sourceRawLayerMap T F a b n =
      sourceBoundaryLayerMap T F a b n ≫ boundaryInclusion (sourceChange T F) a b n := rfl

/-- Source change retains the same original consecutive normalized-layer inclusions. -/
theorem sourceLayerMap_inclusion (T : Data C) (F : C ⟶ D) (a b : O) (n : ℕ) :
    layerInclusion T a b n ≫ sourceLayerMap T F a b (n + 1) =
      sourceLayerMap T F a b n ≫ layerInclusion (sourceChange T F) a b n := rfl

/-- The entire zero layer source map is the SAME original full Hom map in zero-word coordinates. -/
theorem sourceLayerMap_zero_square (T : Data C) (F : C ⟶ D) (a b : O) :
    (zeroLayerIso T a b).hom ≫ sourceLayerMap T F a b 0 =
      homMap F a b ≫ (zeroLayerIso (sourceChange T F) a b).hom := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  apply Subtype.ext
  exact sourceChangeMap_old T F q p

/-- Every full original normalized layer map is weak from honest original source Hom weakness. -/
theorem sourceLayerMap_weak (T : Data C) (F : C ⟶ D)
    (hF : FixedObjectModel.weakEquivalences O F) (a b : O) (n : ℕ) :
    SSet.realizationWeakEquivalences (sourceLayerMap T F a b n) := by
  induction n with
  | zero =>
    exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
      (Arrow.isoMk' _ _ (zeroLayerIso T a b) (zeroLayerIso (sourceChange T F) a b)
        (sourceLayerMap_zero_square T F a b))).mp
      ((FixedObjectModel.weakEquivalences_iff F).mp hF a b)
  | succ n ih =>
    let _ : WeakEquivalence (sourceBoundaryLayerMap T F a b n) :=
      (weakEquivalence_iff _).mpr (sourceBoundaryLayerMap_weak T F hF a b n)
    let _ : WeakEquivalence (sourceRawLayerMap T F a b n) :=
      (weakEquivalence_iff _).mpr (sourceRawLayerMap_weak T F hF a b n)
    let _ : WeakEquivalence (sourceLayerMap T F a b n) := (weakEquivalence_iff _).mpr ih
    let _ : Mono (boundaryInclusion T a b n) := by
      rw [NatTrans.mono_iff_mono_app]
      intro q
      apply (CategoryTheory.mono_iff_injective _).mpr
      intro p r h
      apply Subtype.ext
      exact congrArg (fun t : (rawLayer T a b n).toSSet.obj q => t.val) h
    let _ : Mono (boundaryInclusion (sourceChange T F) a b n) := by
      rw [NatTrans.mono_iff_mono_app]
      intro q
      apply (CategoryTheory.mono_iff_injective _).mpr
      intro p r h
      apply Subtype.ext
      exact congrArg (fun t : (rawLayer (sourceChange T F) a b n).toSSet.obj q => t.val) h
    let _ : Cofibration (boundaryInclusion T a b n) := (cofibration_iff _).mpr
      (inferInstance : Mono (boundaryInclusion T a b n))
    let _ : Cofibration (boundaryInclusion (sourceChange T F) a b n) := (cofibration_iff _).mpr
      (inferInstance : Mono (boundaryInclusion (sourceChange T F) a b n))
    exact (weakEquivalence_iff _).mp (weakEquivalence_map_of_isPushouts_of_cofibrant
      (simplicialLayerIsPushout T a b n).flip (simplicialLayerIsPushout (sourceChange T F) a b n).flip
      (sourceBoundaryLayerMap_inclusion T F a b n) (sourceBoundaryLayerMap_normalize T F a b n)
      (sourceRawLayerMap_normalize T F a b n) (sourceLayerMap_inclusion T F a b n))

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
