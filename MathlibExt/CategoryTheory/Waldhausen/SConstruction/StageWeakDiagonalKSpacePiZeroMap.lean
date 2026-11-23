/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.LoopComponentsMap
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceIdentity
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceComposition

/-!
# Exact-functor maps on weak-diagonal K-space components

An additive exact functor between exact categories in the same universes
induces a map on path components of the one-fold weak-diagonal K-space.  The
map is the generic `loopComponentsMap` associated to the landed realization
map and its explicit mapped-zero-to-target-zero root path.

The representative theorem identifies this map with
`stageWeakDiagonalKSpaceMap`.  Identity and composition therefore become
strict equalities after taking path components, using the existing pointwise
endpoint-fixed homotopies.  The raw K-space functions themselves remain only
homotopy-functorial.

This module constructs a functorial map of component sets.  It does not
construct a continuous loop-space map, a group structure on components, a
weak equivalence, or a natural isomorphism.  Its same-universe restriction is
inherited from `stageWeakDiagonalReal.map`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

section SameUniversePiZeroMap

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

/-- The exact-functor map on path components of the one-fold weak-diagonal
K-space. -/
noncomputable def stageWeakDiagonalKSpacePiZeroMap :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      ZerothHomotopy (stageWeakDiagonalKSpace C) →
        ZerothHomotopy (stageWeakDiagonalKSpace D)) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  exact loopComponentsMap
    (stageWeakDiagonalReal.map C D F).hom
    (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F)

/-- On a loop representative, the component map is represented by the
landed conjugated K-space map. -/
@[simp]
theorem stageWeakDiagonalKSpacePiZeroMap_mk
    (gamma : (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      stageWeakDiagonalKSpace C)) :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonalKSpacePiZeroMap C D F (ZerothHomotopy.mk gamma) =
        ZerothHomotopy.mk (stageWeakDiagonalKSpaceMap C D F gamma)) := by
  change loopComponentsMap (stageWeakDiagonalReal.map C D F).hom
      (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F)
      (ZerothHomotopy.mk gamma) =
    ZerothHomotopy.mk
      ((stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).symm.trans
        ((gamma.map (stageWeakDiagonalReal.map C D F).hom.continuous).trans
          (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F)))
  exact loopComponentsMap_mk (stageWeakDiagonalReal.map C D F).hom
    (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F) gamma

/-- The identity exact functor induces the identity map on K-space path
components.  This is not a strict identity theorem for the raw K-space map. -/
@[simp]
theorem stageWeakDiagonalKSpacePiZeroMap_id :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      stageWeakDiagonalKSpacePiZeroMap C C (Functor.id C) = id) := by
  funext q
  induction q using ZerothHomotopy.rec with
  | mk gamma =>
      rw [stageWeakDiagonalKSpacePiZeroMap_mk]
      exact zerothHomotopy_mk_eq_of_pathHomotopic
        (stageWeakDiagonalKSpaceMap_id_homotopic C gamma)

variable (E : Type u) [Category.{v} E] [Preadditive E]
  [Limits.HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable (G : D ⥤ E) [G.Additive] [Functor.IsExact G]

/-- Composition is strict on K-space path components, with orientation
`G` after `F`.  The underlying raw K-space maps remain related only by the
landed pointwise homotopy. -/
theorem stageWeakDiagonalKSpacePiZeroMap_comp :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategory E := ExactCategory.waldhausenCategory E;
      stageWeakDiagonalKSpacePiZeroMap C E (F ⋙ G) =
        stageWeakDiagonalKSpacePiZeroMap D E G ∘
          stageWeakDiagonalKSpacePiZeroMap C D F) := by
  funext q
  induction q using ZerothHomotopy.rec with
  | mk gamma =>
      simp only [stageWeakDiagonalKSpacePiZeroMap_mk, Function.comp_apply]
      exact zerothHomotopy_mk_eq_of_pathHomotopic
        (stageWeakDiagonalKSpaceMap_comp_homotopic C D F E G gamma)

end SameUniversePiZeroMap

end CategoryTheory.Waldhausen.SConstruction

end
