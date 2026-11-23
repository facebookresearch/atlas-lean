/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzagWeaklyPointed
public import MathlibExt.Topology.Category.TopCat.RealizedPointCofibration
public import MathlibExt.Topology.CWComplex.BasedWhitehead

/-!
# Both original Q/S zigzag legs have actual based inverse data

For the original fixed exact category, both native realization carriers have
the actual max(u,v) universe. Actual zigzag weakness and selected-zero laws,
together with actual realized-vertex point cofibrations, construct both full
point-relative inverse families for the EXACT original forward maps.
No caller CW/model/inverse family is supplied. Mixed-functor calibration
and the original chosen loop-root transport remain further obligations.
-/

public section

noncomputable section

open CategoryTheory Limits HomotopicalAlgebra
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Simplicial TopCat.modelCategory Topology

universe u v w

namespace AlgebraicKTheory

/-- Actual inverse data for a specified original native based map. The
forward map is the original parameter, and both inverse families are whole. -/
structure OriginalQuillenZigzagBasedInverse (X Y : TopCat.{w}) (x : X) (y : Y)
    (f : X ⟶ Y) where
  /-- The original continuous inverse on the full realization carrier. -/
  invFun : C(Y, X)
  /-- The inverse takes the specified target basepoint `y` to the source
  basepoint `x`. -/
  inv_basepoint : invFun y = x
  /-- The complete source inverse homotopy, relative to the original source point. -/
  left : ContinuousMap.HomotopyRel (invFun.comp f.hom) (ContinuousMap.id X) {x}
  /-- The complete target inverse homotopy, relative to the original target point. -/
  right : ContinuousMap.HomotopyRel (f.hom.comp invFun) (ContinuousMap.id Y) {y}

private theorem originalLiteralBasedInverseExists
    (X Y : TopCat.{w}) (x : X) (y : Y)
    [Cofibration (TopCat.const x : TopCat.of PUnit.{w + 1} ⟶ X)]
    [Cofibration (TopCat.const y : TopCat.of PUnit.{w + 1} ⟶ Y)]
    (f : X ⟶ Y) (hxy : f x = y) (hf : TopCat.weakHomotopyEquivalences f) :
    Nonempty (OriginalQuillenZigzagBasedInverse X Y x y f) := by
  obtain ⟨g, hg, ⟨L⟩, ⟨R⟩⟩ :=
    TopCat.exists_based_inverse_of_weak_of_cofibrant_points X Y x y f hxy hf
  refine ⟨{ invFun := g.hom, inv_basepoint := hg, left := ?_, right := ?_ }⟩
  · exact L.cast (TopCat.hom_comp f g) (TopCat.hom_id (X := X))
  · exact R.cast (TopCat.hom_comp g f) (TopCat.hom_id (X := Y))

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The standard Waldhausen structure on the original exact category `C`. -/
local instance originalZigzagWaldhausen : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

private theorem originalQZigzagBasedInverseExists :
    Nonempty (OriginalQuillenZigzagBasedInverse
      (quillenStageGridDiagonalReal C) (NQReal C)
      (quillenStageGridDiagonalReal.basepoint C) (NQReal.basepoint C)
      (SSet.toTop.map (quillenStageGridToNQ (C := C)))) := by
  let X := quillenStageGridDiagonalReal C
  let Y := NQReal C
  let x := quillenStageGridDiagonalReal.basepoint C
  let y := NQReal.basepoint C
  letI : Cofibration (TopCat.const x : TopCat.of PUnit.{max u v + 1} ⟶ X) :=
    SSet.realizedVertex_pointMap_cofibration (quillenStageGridDiagonal C)
      (quillenStageGridDiagonalZeroVertex (C := C))
  letI : Cofibration (TopCat.const y : TopCat.of PUnit.{max u v + 1} ⟶ Y) := by
    dsimp only [y]
    rw [NQReal.basepoint_eq_realizedVertex C]
    exact SSet.realizedVertex_pointMap_cofibration (NQ C) (NQ.zeroVertex C)
  exact originalLiteralBasedInverseExists X Y x y
    (SSet.toTop.map (quillenStageGridToNQ (C := C)))
    (quillenStageGridToNQ_map_basepoint C)
    (quillenStageGridToNQ_mem_realizationWeakEquivalences (C := C))

private theorem originalStageZigzagBasedInverseExists :
    Nonempty (OriginalQuillenZigzagBasedInverse
      (quillenStageGridDiagonalReal C) (stageWeakDiagonalReal C)
      (quillenStageGridDiagonalReal.basepoint C) (stageWeakDiagonalReal.basepoint C)
      (SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := C)))) := by
  let X := quillenStageGridDiagonalReal C
  let Y := stageWeakDiagonalReal C
  let x := quillenStageGridDiagonalReal.basepoint C
  let y := stageWeakDiagonalReal.basepoint C
  letI : Cofibration (TopCat.const x : TopCat.of PUnit.{max u v + 1} ⟶ X) :=
    SSet.realizedVertex_pointMap_cofibration (quillenStageGridDiagonal C)
      (quillenStageGridDiagonalZeroVertex (C := C))
  letI : Cofibration (TopCat.const y : TopCat.of PUnit.{max u v + 1} ⟶ Y) := by
    dsimp only [y]
    rw [stageWeakDiagonalReal.basepoint_eq_realizedVertex C]
    exact SSet.realizedVertex_pointMap_cofibration (stageWeakDiagonal C)
      (stageWeakDiagonalZeroVertex C)
  have hPoint : SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := C)) x = y := by
    exact (quillenStageGridToStageWeakDiagonal_realizedZeroVertex (C := C)).trans
      (stageWeakDiagonalReal.basepoint_eq_realizedVertex C).symm
  exact originalLiteralBasedInverseExists X Y x y
    (SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := C))) hPoint
    (quillenStageGridToStageWeakDiagonal_mem_realizationWeakEquivalences (C := C))

/-- Chosen based inverse data for the EXACT original Q-side forward map,
with both whole original singleton-relative inverse families. -/
def quillenOriginalQZigzagBasedInverse : OriginalQuillenZigzagBasedInverse
    (quillenStageGridDiagonalReal C) (NQReal C)
    (quillenStageGridDiagonalReal.basepoint C) (NQReal.basepoint C)
    (SSet.toTop.map (quillenStageGridToNQ (C := C))) :=
  Classical.choice (originalQZigzagBasedInverseExists C)

/-- Chosen based inverse data for the EXACT original factored Stage-side
forward map, with both whole original singleton-relative inverse families. -/
def quillenOriginalStageZigzagBasedInverse : OriginalQuillenZigzagBasedInverse
    (quillenStageGridDiagonalReal C) (stageWeakDiagonalReal C)
    (quillenStageGridDiagonalReal.basepoint C) (stageWeakDiagonalReal.basepoint C)
    (SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := C))) :=
  Classical.choice (originalStageZigzagBasedInverseExists C)

/-- The Q-side equivalence retains EXACT original forward map and the
SAME chosen inverse and both actual relative inverse families. -/
def quillenOriginalQZigzagHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (quillenStageGridDiagonalReal C) (NQReal C) where
  toFun := (SSet.toTop.map (quillenStageGridToNQ (C := C))).hom
  invFun := (quillenOriginalQZigzagBasedInverse C).invFun
  left_inv := ⟨(quillenOriginalQZigzagBasedInverse C).left.toHomotopy⟩
  right_inv := ⟨(quillenOriginalQZigzagBasedInverse C).right.toHomotopy⟩

/-- The Stage-side equivalence retains EXACT original factored forward map
and the SAME chosen inverse and both actual relative inverse families. -/
def quillenOriginalStageZigzagHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (quillenStageGridDiagonalReal C) (stageWeakDiagonalReal C) where
  toFun := (SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := C))).hom
  invFun := (quillenOriginalStageZigzagBasedInverse C).invFun
  left_inv := ⟨(quillenOriginalStageZigzagBasedInverse C).left.toHomotopy⟩
  right_inv := ⟨(quillenOriginalStageZigzagBasedInverse C).right.toHomotopy⟩

/-- Every original Q-side root-path time has the original selected Q zero. -/
theorem quillenOriginalQZigzag_root_constant (t : unitInterval) :
    (quillenStageGridToNQWeaklyPointed (C := C)).rootPath.toContinuousMap.toFun t =
      NQReal.basepoint C := rfl

/-- Every original Stage-side composed root-path time has the original
selected Stage zero, with the ACTUAL original root-trans clock retained. -/
theorem quillenOriginalStageZigzag_root_constant (t : unitInterval) :
    (quillenStageGridToStageWeaklyPointed (C := C)).rootPath.toContinuousMap.toFun t =
      stageWeakDiagonalReal.basepoint C := by
  let A := quillenStageGridStageProjectionWeaklyPointed (C := C)
  let B := outerEdgewiseStageDiagonalComparisonWeaklyPointed (C := C)
  change ((A.rootPath.map B.hom.continuous).trans B.rootPath) t = _
  rw [Path.trans_apply]
  split_ifs
  · exact outerEdgewiseStageDiagonalComparison_map_basepoint C
  · rfl


private theorem originalQZigzagEquivForwardComputed :
    (quillenOriginalQZigzagHomotopyEquiv C).toFun =
      (quillenStageGridToNQWeaklyPointed (C := C)).hom := rfl
/-- The actual based Q-side equivalence retains the WHOLE original weak-leg map. -/
theorem quillenOriginalQZigzagHomotopyEquiv_toFun :
    (quillenOriginalQZigzagHomotopyEquiv C).toFun =
      (quillenStageGridToNQWeaklyPointed (C := C)).hom :=
  originalQZigzagEquivForwardComputed C

private theorem originalStageZigzagEquivForwardComputed :
    (quillenOriginalStageZigzagHomotopyEquiv C).toFun =
      (quillenStageGridToStageWeaklyPointed (C := C)).hom := by
  exact (quillenStageGridToStageWeaklyPointed_hom (C := C)).symm
/-- The actual based Stage-side equivalence retains the WHOLE original composed leg map. -/
theorem quillenOriginalStageZigzagHomotopyEquiv_toFun :
    (quillenOriginalStageZigzagHomotopyEquiv C).toFun =
      (quillenStageGridToStageWeaklyPointed (C := C)).hom :=
  originalStageZigzagEquivForwardComputed C

end AlgebraicKTheory

end


public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Topology

universe u v

namespace AlgebraicKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
/-- The standard Waldhausen structure on the original exact category `C`. -/
local instance originalRealInverseValuesWaldhausen : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

private theorem originalQRealInverseValueComputed :
    (quillenOriginalQZigzagHomotopyEquiv C).invFun =
      (quillenOriginalQZigzagBasedInverse C).invFun := rfl
private theorem originalStageRealInverseValueComputed :
    (quillenOriginalStageZigzagHomotopyEquiv C).invFun =
      (quillenOriginalStageZigzagBasedInverse C).invFun := rfl

/-- EXACT original Q-side based inverse map, on the complete original carrier. -/
theorem quillenOriginalQZigzagHomotopyEquiv_invFun :
    (quillenOriginalQZigzagHomotopyEquiv C).invFun =
      (quillenOriginalQZigzagBasedInverse C).invFun := originalQRealInverseValueComputed C
/-- EXACT original Stage-side based inverse map, on the complete original carrier. -/
theorem quillenOriginalStageZigzagHomotopyEquiv_invFun :
    (quillenOriginalStageZigzagHomotopyEquiv C).invFun =
      (quillenOriginalStageZigzagBasedInverse C).invFun := originalStageRealInverseValueComputed C

/-- BOTH original Q relative inverse families, typed at SAME original equivalence maps. -/
def quillenOriginalQZigzagRealLeftFamily :
    ContinuousMap.HomotopyRel
      ((quillenOriginalQZigzagHomotopyEquiv C).invFun.comp
        (quillenOriginalQZigzagHomotopyEquiv C).toFun)
      (ContinuousMap.id (quillenStageGridDiagonalReal C))
      {quillenStageGridDiagonalReal.basepoint C} :=
  (quillenOriginalQZigzagBasedInverse C).left

/-- The complete original Q-side real inverse family, relative to the selected Q basepoint. -/
def quillenOriginalQZigzagRealRightFamily :
    ContinuousMap.HomotopyRel
      ((quillenOriginalQZigzagHomotopyEquiv C).toFun.comp
        (quillenOriginalQZigzagHomotopyEquiv C).invFun)
      (ContinuousMap.id (NQReal C)) {NQReal.basepoint C} :=
  (quillenOriginalQZigzagBasedInverse C).right

/-- BOTH original Stage relative inverse families, at SAME original equivalence maps. -/
def quillenOriginalStageZigzagRealLeftFamily :
    ContinuousMap.HomotopyRel
      ((quillenOriginalStageZigzagHomotopyEquiv C).invFun.comp
        (quillenOriginalStageZigzagHomotopyEquiv C).toFun)
      (ContinuousMap.id (quillenStageGridDiagonalReal C))
      {quillenStageGridDiagonalReal.basepoint C} :=
  (quillenOriginalStageZigzagBasedInverse C).left

/-- The complete original stage-side real inverse family, relative to the selected stage basepoint. -/
def quillenOriginalStageZigzagRealRightFamily :
    ContinuousMap.HomotopyRel
      ((quillenOriginalStageZigzagHomotopyEquiv C).toFun.comp
        (quillenOriginalStageZigzagHomotopyEquiv C).invFun)
      (ContinuousMap.id (stageWeakDiagonalReal C)) {stageWeakDiagonalReal.basepoint C} :=
  (quillenOriginalStageZigzagBasedInverse C).right

end AlgebraicKTheory

end
