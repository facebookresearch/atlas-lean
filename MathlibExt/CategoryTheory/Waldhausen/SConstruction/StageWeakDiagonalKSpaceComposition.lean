/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceMap
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceCompositionPath
public import MathlibExt.Topology.Homotopy.PathConjugationHomotopic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# K-space composition law up to endpoint-fixed homotopy for G4

For exact categories `C`, `D`, `E` over the same universes with additive exact
`F : C ⥤ D` and `G : D ⥤ E`, the direct K-space map for `F ⋙ G` is
endpoint-fixed homotopic to the iterated maps, pointwise in `γ`, with the
orientation `Map (F ⋙ G) γ ~ Map G (Map F γ)`.

Strict rewrites use `stageWeakDiagonalReal.map_comp` with `Path.map_trans`,
`Path.map_symm`, and casts. Homotopy steps use
`zeroComparisonRootPath_comp_homotopic` with
`mappedZeroComparisonRootPath_homotopic` and `Path.Homotopic.conj_transport`,
`hcomp`, `trans`, and `pathCast`. One public pointwise homotopy only.

No strict map equality or bundled functor, additivity, pi-zero identification,
spectra, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]
variable (E : Type u) [Category.{v} E] [Preadditive E]
  [Limits.HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable (G : D ⥤ E) [G.Additive] [Functor.IsExact G]

/-- Strict morphism-level composition, reused for point alignment. -/
private theorem kspace_real_map_comp :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategory E := ExactCategory.waldhausenCategory E;
      stageWeakDiagonalReal.map C E (F ⋙ G) =
        stageWeakDiagonalReal.map C D F ≫ stageWeakDiagonalReal.map D E G) :=
  stageWeakDiagonalReal.map_comp C D F E G

/-- Strict basepoint image alignment via the morphism law. -/
private theorem kspace_mapped_basepoint_eq :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategory E := ExactCategory.waldhausenCategory E;
      (stageWeakDiagonalReal.map C E (F ⋙ G)) (stageWeakDiagonalReal.basepoint C) =
        (stageWeakDiagonalReal.map D E G)
          ((stageWeakDiagonalReal.map C D F) (stageWeakDiagonalReal.basepoint C))) := by
  simp [kspace_real_map_comp C D F E G]

/-- Pointwise composition homotopy for K-space maps.

Orientation (do not flip): direct `(F ⋙ G)` map on the left, iterated
`G`-after-`F` map on the right. Same-universe exact-category hypotheses.
Strict rewrites are separated from homotopy steps below. -/
theorem stageWeakDiagonalKSpaceMap_comp_homotopic :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategory E := ExactCategory.waldhausenCategory E;
      ∀ γ : stageWeakDiagonalKSpace C,
        (stageWeakDiagonalKSpaceMap C E (F ⋙ G) γ).Homotopic
          (stageWeakDiagonalKSpaceMap D E G
            (stageWeakDiagonalKSpaceMap C D F γ))) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategory E := ExactCategory.waldhausenCategory E
  intro γ
  -- Strict rewrites: pointwise morphism law and loop alignment, no homotopy.
  have hMapComp := kspace_real_map_comp C D F E G
  have hPt := kspace_mapped_basepoint_eq C D F E G
  have hFun : ∀ y, (stageWeakDiagonalReal.map C E (F ⋙ G)) y =
      (stageWeakDiagonalReal.map D E G) ((stageWeakDiagonalReal.map C D F) y) := by
    intro y
    simp only [hMapComp, TopCat.hom_comp, ContinuousMap.comp_apply]
  have hLoopDirect : stageWeakDiagonalKSpace.mapLoop C E (F ⋙ G) γ =
      (((stageWeakDiagonalKSpace.mapLoop C D F γ).map
        (map_continuous (stageWeakDiagonalReal.map D E G).hom)).cast
        hPt hPt) := by
    apply Path.ext
    ext t
    simp only [stageWeakDiagonalKSpace.mapLoop, Path.cast_coe]
    exact hFun _
  -- Homotopy steps: root-path composition with mapped bridge.
  have hRoot := stageWeakDiagonalKSpace.zeroComparisonRootPath_comp_homotopic
    C D F E G
  have hMapInner :
      stageWeakDiagonalKSpace.mapLoop D E G
        ((stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).symm.trans
          ((stageWeakDiagonalKSpace.mapLoop C D F γ).trans
            (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F))) =
        (((stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).map
          (map_continuous (stageWeakDiagonalReal.map D E G).hom)).symm.trans
          ((((stageWeakDiagonalKSpace.mapLoop C D F γ).map
            (map_continuous (stageWeakDiagonalReal.map D E G).hom)).trans
            ((stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).map
              (map_continuous (stageWeakDiagonalReal.map D E G).hom))))) := by
    change (((stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).symm.trans
      ((stageWeakDiagonalKSpace.mapLoop C D F γ).trans
        (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F))).map
      (map_continuous (stageWeakDiagonalReal.map D E G).hom) = _)
    rw [Path.map_trans, Path.map_trans, ← Path.map_symm]
  -- Unfold maps to conjugation form.
  simp only [stageWeakDiagonalKSpaceMap]
  rw [hLoopDirect, hMapInner]
  -- Transport the direct conjugate along the root-path homotopy.
  have hConjDirect := Path.Homotopic.conj_transport (γ :=
      (((stageWeakDiagonalKSpace.mapLoop C D F γ).map
        (map_continuous (stageWeakDiagonalReal.map D E G).hom)).cast
        hPt hPt)) hRoot
  -- Combine root homotopy with mapped-loop congruence.
  -- Reassociate the intermediate conjugate into nested pG/mapped-F form.
  refine hConjDirect.trans ?_
  rw [Path.trans_symm _ _]
  refine (Path.Homotopic.trans_assoc _ _ _).trans ?_
  refine (Path.Homotopic.refl _).hcomp ?_
  refine ((Path.Homotopic.refl _).hcomp (Path.Homotopic.trans_assoc _ _ _).symm).trans ?_
  refine (Path.Homotopic.trans_assoc _ _ _).symm.trans ?_
  exact Path.Homotopic.refl _

end CategoryTheory.Waldhausen.SConstruction
