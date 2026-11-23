/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceComposition
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceIdentity
public import MathlibExt.Topology.Homotopy.WeaklyPointedMap

/-!
# Continuous exact-functor maps on the weak-diagonal K-space

An additive exact functor already induces a realized weak-diagonal map and a
chosen path from the mapped zero basepoint to the target zero basepoint.  This
file packages those data as a `ContinuousMap.WeaklyPointed` map and applies the
generic continuous `loopMap` construction.

The resulting continuous map is pointwise equal to the existing raw
`stageWeakDiagonalKSpaceMap`.  Its identity and composition laws therefore
reuse the existing endpoint-fixed path homotopies with their original
orientation.

This file makes no strict functoriality, exact-functor additivity naturality,
weak-homotopy-equivalence, homotopy-equivalence, inverse, spectrum, or Q/S
claim, and installs no global Waldhausen or homotopical instance.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

/-- The realized exact-functor map, weakly pointed by the existing
mapped-zero-to-target-zero path. -/
noncomputable def stageWeakDiagonalRealMapWeaklyPointed :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      ContinuousMap.WeaklyPointed
        (stageWeakDiagonalReal.basepoint C)
        (stageWeakDiagonalReal.basepoint D)) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  exact
    { hom := (stageWeakDiagonalReal.map C D F).hom
      rootPath := stageWeakDiagonalKSpace.zeroComparisonRootPath C D F }

/-- The underlying continuous map is the landed realization map. -/
@[simp]
theorem stageWeakDiagonalRealMapWeaklyPointed_hom :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalRealMapWeaklyPointed C D F).hom =
        (stageWeakDiagonalReal.map C D F).hom) := by
  rfl

/-- The weakly pointed root path is exactly the landed zero-comparison path. -/
@[simp]
theorem stageWeakDiagonalRealMapWeaklyPointed_rootPath :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalRealMapWeaklyPointed C D F).rootPath =
        stageWeakDiagonalKSpace.zeroComparisonRootPath C D F) := by
  rfl

/-- Continuous exact-functor map on the one-fold weak-diagonal K-space. -/
noncomputable def stageWeakDiagonalKSpaceContinuousMap :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      C(stageWeakDiagonalKSpace C, stageWeakDiagonalKSpace D)) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  exact (stageWeakDiagonalRealMapWeaklyPointed C D F).loopMap

/-- The continuous map has the same conjugation formula as the existing raw
K-space map. -/
@[simp]
theorem stageWeakDiagonalKSpaceContinuousMap_apply
    (gamma : (letI : WaldhausenCategory C :=
        ExactCategory.waldhausenCategory C;
      stageWeakDiagonalKSpace C)) :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonalKSpaceContinuousMap C D F gamma =
        stageWeakDiagonalKSpaceMap C D F gamma) := by
  rfl

/-- The continuous map of the identity exact functor is pointwise homotopic
to the identity. -/
theorem stageWeakDiagonalKSpaceContinuousMap_id_homotopic
    (gamma : (letI : WaldhausenCategory C :=
        ExactCategory.waldhausenCategory C;
      stageWeakDiagonalKSpace C)) :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      (stageWeakDiagonalKSpaceContinuousMap C C (𝟭 C) gamma).Homotopic gamma) := by
  simpa only [stageWeakDiagonalKSpaceContinuousMap_apply] using
    stageWeakDiagonalKSpaceMap_id_homotopic C gamma

/-- Continuous exact-functor K-space maps respect composition pointwise up to
the existing endpoint-fixed homotopy. -/
theorem stageWeakDiagonalKSpaceContinuousMap_comp_homotopic
    (E : Type u) [Category.{v} E] [Preadditive E]
    [Limits.HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
    (G : D ⥤ E) [G.Additive] [Functor.IsExact G]
    (gamma : (letI : WaldhausenCategory C :=
        ExactCategory.waldhausenCategory C;
      stageWeakDiagonalKSpace C)) :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategory E := ExactCategory.waldhausenCategory E;
      (stageWeakDiagonalKSpaceContinuousMap C E (F ⋙ G) gamma).Homotopic
        (stageWeakDiagonalKSpaceContinuousMap D E G
          (stageWeakDiagonalKSpaceContinuousMap C D F gamma))) := by
  simpa only [stageWeakDiagonalKSpaceContinuousMap_apply] using
    stageWeakDiagonalKSpaceMap_comp_homotopic C D F E G gamma

end CategoryTheory.Waldhausen.SConstruction

end
