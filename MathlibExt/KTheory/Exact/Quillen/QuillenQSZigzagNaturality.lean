/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMapNerve
public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzag
public import MathlibExt.KTheory.Exact.Quillen.Realization
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealizationMap

/-!
# Exact-functor naturality of the Quillen Q/S zigzag

At common source and target universes, the retained-discrete-Q diagonal
comparison and the outer-edgewise Stage comparison commute with additive
exact functors.  Combining these endpoint squares with the Stage-grid
projection squares gives strict naturality of both simplicial legs of the
Quillen Q/S zigzag.  Geometric realization preserves these equalities
strictly.

This file constructs no weakly pointed map or root path, loop map, weak
equivalence, chosen inverse, direct Q/S equivalence, group comparison, or
spectrum map.  It also asserts no strict identity or composition law for the
exact-functor Stage-grid map.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

local instance quillenQSZigzagNaturalityWaldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

local instance quillenQSZigzagNaturalityWaldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

/-- The discrete-diagonal comparison with the ordinary Quillen nerve is
natural in additive exact functors. -/
theorem quillenQSimplexDiscreteDiagonalIso_naturality :
    quillenQSimplexDiscreteDiagonalMap F ≫
        (quillenQSimplexDiscreteDiagonalIso (C := D)).hom =
      (quillenQSimplexDiscreteDiagonalIso (C := C)).hom ≫ NQ.map F := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- The outer-edgewise Stage comparison is natural in additive exact
functors. -/
theorem outerEdgewiseStageDiagonalComparison_naturality :
    edgewiseStageWeakDiagonalMap F ≫
        outerEdgewiseStageDiagonalComparison (C := D) =
      outerEdgewiseStageDiagonalComparison (C := C) ≫
        stageWeakDiagonalMap C D F := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro x
  change ((stageWeakNerve D).map
      (SimplexCategory.edgewiseRightInclusion.app a.unop).op).app a
        (((stageWeakNerveMap C D F).app
          (SimplexCategory.edgewiseQ.op.obj a)).app a x) =
    ((stageWeakNerveMap C D F).app a).app a
      (((stageWeakNerve C).map
        (SimplexCategory.edgewiseRightInclusion.app a.unop).op).app a x)
  have h := NatTrans.congr_app ((stageWeakNerveMap C D F).naturality
    (SimplexCategory.edgewiseRightInclusion.app a.unop).op) a
  exact ConcreteCategory.congr_hom h.symm x

/-- The literal Stage-grid-to-Quillen simplicial leg is natural in additive
exact functors. -/
theorem quillenStageGridToNQ_naturality :
    quillenStageGridDiagonalMap F ≫
        quillenStageGridToNQ (C := D) =
      quillenStageGridToNQ (C := C) ≫ NQ.map F := by
  unfold quillenStageGridToNQ
  rw [← Category.assoc,
    quillenStageGridQProjectionDiagonal_naturality F,
    Category.assoc,
    quillenQSimplexDiscreteDiagonalIso_naturality F,
    ← Category.assoc]

/-- The literal Stage-grid-to-weak-Stage simplicial leg is natural in additive
exact functors. -/
theorem quillenStageGridToStageWeakDiagonal_naturality :
    quillenStageGridDiagonalMap F ≫
        quillenStageGridToStageWeakDiagonal (C := D) =
      quillenStageGridToStageWeakDiagonal (C := C) ≫
        stageWeakDiagonalMap C D F := by
  unfold quillenStageGridToStageWeakDiagonal
  rw [← Category.assoc,
    quillenStageGridStageProjectionDiagonal_naturality F,
    Category.assoc,
    outerEdgewiseStageDiagonalComparison_naturality F,
    ← Category.assoc]

/-- The realized map induced by the exact-functor map of Stage-grid
diagonals. -/
noncomputable def quillenStageGridDiagonalRealMap :
    SSet.toTop.obj (quillenStageGridDiagonal C) ⟶
      SSet.toTop.obj (quillenStageGridDiagonal D) :=
  SSet.toTop.map (quillenStageGridDiagonalMap F)

/-- The realized Stage-grid-to-Quillen leg is strictly natural in additive
exact functors. -/
theorem quillenStageGridToNQ_realization_naturality :
    quillenStageGridDiagonalRealMap F ≫
        SSet.toTop.map (quillenStageGridToNQ (C := D)) =
      SSet.toTop.map (quillenStageGridToNQ (C := C)) ≫
        NQReal.map F := by
  simpa only [quillenStageGridDiagonalRealMap, NQReal.map,
    ← SSet.toTop.map_comp] using congrArg SSet.toTop.map
      (quillenStageGridToNQ_naturality F)

/-- The realized Stage-grid-to-weak-Stage leg is strictly natural in additive
exact functors. -/
theorem quillenStageGridToStage_realization_naturality :
    quillenStageGridDiagonalRealMap F ≫
        SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := D)) =
      SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := C)) ≫
        stageWeakDiagonalReal.map C D F := by
  simpa only [quillenStageGridDiagonalRealMap,
    stageWeakDiagonalReal.map, ← SSet.toTop.map_comp] using
      congrArg SSet.toTop.map
        (quillenStageGridToStageWeakDiagonal_naturality F)

end AlgebraicKTheory

end
