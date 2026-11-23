/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Exact.Quillen.QuillenOuterEdgewiseStageComparison
public import
  MathlibExt.KTheory.Exact.Quillen.QuillenStageGridQProjectionWeakEquivalence
public import
  MathlibExt.KTheory.Exact.Quillen.QuillenStageGridStageProjectionWeakEquivalence

/-!
# The unpointed Quillen Q/S zigzag

The diagonal nerve of Quillen Stage-grid lifts has a realization weak
equivalence to the Quillen Q-nerve and a realization weak equivalence to the
outer-edgewise weak-Stage diagonal.  Composing the latter with the literal
outer-edgewise Stage comparison gives the ordinary weak-Stage endpoint:

```text
NQ C  <-  quillenStageGridDiagonal C
              -> edgewiseStageWeakDiagonal C -> stageWeakDiagonal C.
```

One canonical grid vertex, built from the pointwise-zero degree-one Stage
with identity agreement, maps literally to the selected zero vertex at every
stage of this zigzag.  The corresponding realized vertices are therefore
preserved as equal points.

This file constructs no inverse or map from `NQ C` to `stageWeakDiagonal C`.
It also makes no pointed-map, loop-space, homotopy-equivalence, spectrum, or
exact-functor-naturality claim.
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

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenQSZigzagWaldhausenCategory : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- The canonical zero vertex of the diagonal Stage-grid nerve.  Its material
Stage is the pointwise-zero degree-one Stage, and its retained Quillen
simplex is the one extracted from that Stage with identity agreement. -/
noncomputable def quillenStageGridDiagonalZeroVertex :
    (quillenStageGridDiagonal C).obj (op ⦋0⦌) :=
  ComposableArrows.mk₀
    (QuillenStageGridLift.ofGrid
      (⟨⟨zeroDiagram C 1, isStage_zeroDiagram C 1⟩⟩ :
        StageWeakCategory C 1))

/-- The Stage projection sends the canonical grid zero vertex to the
pointwise-zero outer-edgewise Stage vertex. -/
@[simp]
theorem quillenStageGridStageProjectionDiagonal_zeroVertex :
    (quillenStageGridStageProjectionDiagonal (C := C)).app (op ⦋0⦌)
        (quillenStageGridDiagonalZeroVertex (C := C)) =
      edgewiseStageWeakDiagonalZeroVertex (C := C) := by
  unfold quillenStageGridDiagonalZeroVertex
  rw [quillenStageGridStageProjectionDiagonal_app_mk₀]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The retained-Q comparison sends the same canonical grid zero vertex to
the zero vertex of the ordinary Quillen Q-nerve. -/
@[simp]
theorem quillenStageGridToNQ_zeroVertex :
    (quillenStageGridToNQ (C := C)).app (op ⦋0⦌)
        (quillenStageGridDiagonalZeroVertex (C := C)) =
      NQ.zeroVertex C := by
  let A : StageWeakCategory C 1 :=
    ⟨⟨zeroDiagram C 1, isStage_zeroDiagram C 1⟩⟩
  have hzero : quillenStageGridDiagonalZeroVertex (C := C) =
      ComposableArrows.mk₀ (QuillenStageGridLift.ofGrid A) := by
    rfl
  rw [hzero]
  change (quillenQSimplexDiscreteDiagonalIso (C := C)).hom.app (op ⦋0⦌)
      ((CategoryTheory.nerveMap (quillenStageGridQProjection C ⦋0⦌)).app
        (op ⦋0⦌) (ComposableArrows.mk₀
          (QuillenStageGridLift.ofGrid A))) =
    NQ.zeroVertex C
  rw [CategoryTheory.nerveMap_app_mk₀,
    quillenQSimplexDiscreteDiagonalIso_hom_app]
  change (QuillenStageGridLift.ofGrid A).q = NQ.zeroVertex C
  rw [QuillenStageGridLift.ofGrid_q]
  apply ComposableArrows.ext₀
  rfl

/-- The factored right leg of the Q/S zigzag, from the Stage-grid diagonal
through the outer-edgewise weak-Stage diagonal to the ordinary weak-Stage
diagonal. -/
noncomputable def quillenStageGridToStageWeakDiagonal :
    quillenStageGridDiagonal C ⟶ stageWeakDiagonal C :=
  quillenStageGridStageProjectionDiagonal (C := C) ≫
    outerEdgewiseStageDiagonalComparison (C := C)

/-- The factored grid-to-ordinary-Stage comparison is a realization weak
equivalence. -/
theorem quillenStageGridToStageWeakDiagonal_mem_realizationWeakEquivalences :
    SSet.realizationWeakEquivalences
      (quillenStageGridToStageWeakDiagonal (C := C)) := by
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    quillenStageGridStageProjectionDiagonal_mem_realizationWeakEquivalences
    outerEdgewiseStageDiagonalComparison_mem_realizationWeakEquivalences

/-- The factored right leg sends the canonical grid zero vertex to the
canonical ordinary Stage-zero vertex. -/
@[simp]
theorem quillenStageGridToStageWeakDiagonal_zeroVertex :
    (quillenStageGridToStageWeakDiagonal (C := C)).app (op ⦋0⦌)
        (quillenStageGridDiagonalZeroVertex (C := C)) =
      stageWeakDiagonalZeroVertex C := by
  change (outerEdgewiseStageDiagonalComparison (C := C)).app (op ⦋0⦌)
      ((quillenStageGridStageProjectionDiagonal (C := C)).app (op ⦋0⦌)
        (quillenStageGridDiagonalZeroVertex (C := C))) =
    stageWeakDiagonalZeroVertex C
  rw [quillenStageGridStageProjectionDiagonal_zeroVertex,
    outerEdgewiseStageDiagonalComparison_zeroVertex]

/-- The realized Q-side comparison sends the realized canonical grid zero
vertex to the realized Quillen zero vertex. -/
theorem quillenStageGridToNQ_realizedZeroVertex :
    SSet.toTop.map (quillenStageGridToNQ (C := C))
        (SSet.realizedVertex
          (quillenStageGridDiagonalZeroVertex (C := C))) =
      SSet.realizedVertex (NQ.zeroVertex C) := by
  rw [← SSet.realizedVertex_naturality,
    quillenStageGridToNQ_zeroVertex]

/-- The realized elementary Stage projection sends the realized canonical
grid zero vertex to the realized outer-edgewise Stage zero vertex. -/
theorem quillenStageGridStageProjectionDiagonal_realizedZeroVertex :
    SSet.toTop.map
        (quillenStageGridStageProjectionDiagonal (C := C))
        (SSet.realizedVertex
          (quillenStageGridDiagonalZeroVertex (C := C))) =
      SSet.realizedVertex
        (edgewiseStageWeakDiagonalZeroVertex (C := C)) := by
  rw [← SSet.realizedVertex_naturality,
    quillenStageGridStageProjectionDiagonal_zeroVertex]

/-- The realized factored right leg sends the realized canonical grid zero
vertex to the realized ordinary Stage-zero vertex. -/
theorem quillenStageGridToStageWeakDiagonal_realizedZeroVertex :
    SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := C))
        (SSet.realizedVertex
          (quillenStageGridDiagonalZeroVertex (C := C))) =
      SSet.realizedVertex (stageWeakDiagonalZeroVertex C) := by
  rw [← SSet.realizedVertex_naturality,
    quillenStageGridToStageWeakDiagonal_zeroVertex]

end AlgebraicKTheory

end
