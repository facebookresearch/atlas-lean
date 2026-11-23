/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Exact.Quillen.QuillenStageGridZeroComparisonEdge
public import MathlibExt.KTheory.Exact.Quillen.NQKSpaceContinuousMap
public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzagWeaklyPointed
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceContinuousMap

/-!
# Canonical Stage-grid zero-comparison coherence

The explicit three-edge chain of `QuillenStageGridZeroComparisonEdge` gives a
canonical path from the mapped source grid basepoint to the target grid
basepoint.  This file equips the realized exact-functor grid map with that
root path and proves that both weakly pointed legs of the Quillen Q/S zigzag
carry it to their existing Q and Stage root paths, with the exact casts forced
by the strict underlying-map squares.

The result is a canonical `QuillenStageGridZeroComparisonCoherence`.  No loop
map naturality, strict equality of paths or weakly pointed maps, weak
equivalence, group comparison, direct Q/S equivalence, or spectrum map is
constructed here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial ZeroObject
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial Topology

universe w v u

namespace AlgebraicKTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- The canonical Waldhausen structure on the original exact source category. -/
local instance quillenStageGridZeroComparisonCoherenceWaldhausenC :
    WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- The canonical Waldhausen structure on the original exact target category. -/
local instance quillenStageGridZeroComparisonCoherenceWaldhausenD :
    WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

namespace QuillenStageGridZeroComparisonCoherence.Internal

set_option backward.isDefEq.respectTransparency false in
theorem quillenStageGridDiagonalRealMap_basepoint_eq_realized_mappedZeroLift :
    quillenStageGridDiagonalRealMap F
        (quillenStageGridDiagonalReal.basepoint C) =
      SSet.realizedVertex (ComposableArrows.mk₀ (quillenStageGridMappedZeroLift F)) := by
  unfold quillenStageGridDiagonalRealMap
  rw [quillenStageGridDiagonalReal.basepoint]
  rw [← SSet.realizedVertex_naturality]
  apply congrArg SSet.realizedVertex
  change (CategoryTheory.nerveMap
      (quillenStageGridLiftMap F ⦋0⦌)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (quillenStageGridZeroLift C)) = _
  rw [CategoryTheory.nerveMap_app_mk₀]
  rfl

theorem quillenStageGridDiagonalReal_basepoint_eq_realized_targetZeroLift :
    quillenStageGridDiagonalReal.basepoint D =
      SSet.realizedVertex (ComposableArrows.mk₀ (quillenStageGridTargetZeroLift (D := D))) := by
  rfl

end QuillenStageGridZeroComparisonCoherence.Internal

open QuillenStageGridZeroComparisonCoherence.Internal

/-- Root-path data for the realized exact-functor map on the Stage-grid
diagonal. -/
noncomputable abbrev quillenStageGridDiagonalZeroComparisonPathData :=
  Path
    (quillenStageGridDiagonalRealMap F
      (quillenStageGridDiagonalReal.basepoint C))
    (quillenStageGridDiagonalReal.basepoint D)

/-- Canonical grid root obtained by casting the explicit D4-A three-edge path
to the selected realization basepoints. -/
noncomputable def quillenStageGridDiagonalZeroComparisonRootPath :
    quillenStageGridDiagonalZeroComparisonPathData F :=
  (quillenStageGridDiagonalZeroComparisonRawPath F).cast
    (quillenStageGridDiagonalRealMap_basepoint_eq_realized_mappedZeroLift F)
    (quillenStageGridDiagonalReal_basepoint_eq_realized_targetZeroLift (D := D))

/-- The realized exact-functor grid map equipped with a supplied forward root
path. -/
noncomputable def quillenStageGridDiagonalRealMapWeaklyPointed
    (p : quillenStageGridDiagonalZeroComparisonPathData F) :
    ContinuousMap.WeaklyPointed
      (quillenStageGridDiagonalReal.basepoint C)
      (quillenStageGridDiagonalReal.basepoint D) where
  hom := (quillenStageGridDiagonalRealMap F).hom
  rootPath := p

/-- The underlying continuous map is the realized exact-functor grid map. -/
@[simp]
theorem quillenStageGridDiagonalRealMapWeaklyPointed_hom
    (p : quillenStageGridDiagonalZeroComparisonPathData F) :
    (quillenStageGridDiagonalRealMapWeaklyPointed F p).hom =
      (quillenStageGridDiagonalRealMap F).hom :=
  rfl

/-- The weakly pointed grid map uses exactly the supplied root path. -/
@[simp]
theorem quillenStageGridDiagonalRealMapWeaklyPointed_rootPath
    (p : quillenStageGridDiagonalZeroComparisonPathData F) :
    (quillenStageGridDiagonalRealMapWeaklyPointed F p).rootPath = p :=
  rfl

/-- Strict equality of the underlying maps around the grid-to-Q square. -/
theorem quillenStageGridToNQ_weak_square_hom
    (p : quillenStageGridDiagonalZeroComparisonPathData F) :
    ((quillenStageGridDiagonalRealMapWeaklyPointed F p).comp
      (quillenStageGridToNQWeaklyPointed (C := D))).hom =
    ((quillenStageGridToNQWeaklyPointed (C := C)).comp
      (NQRealMapWeaklyPointed F)).hom := by
  change (quillenStageGridDiagonalRealMap F ≫
      SSet.toTop.map (quillenStageGridToNQ (C := D))).hom =
    (SSet.toTop.map (quillenStageGridToNQ (C := C)) ≫
      NQReal.map F).hom
  exact congrArg TopCat.Hom.hom
    (quillenStageGridToNQ_realization_naturality F)

/-- Strict equality of the underlying maps around the grid-to-Stage square. -/
theorem quillenStageGridToStage_weak_square_hom
    (p : quillenStageGridDiagonalZeroComparisonPathData F) :
    ((quillenStageGridDiagonalRealMapWeaklyPointed F p).comp
      (quillenStageGridToStageWeaklyPointed (C := D))).hom =
    ((quillenStageGridToStageWeaklyPointed (C := C)).comp
      (stageWeakDiagonalRealMapWeaklyPointed C D F)).hom := by
  simp only [ContinuousMap.WeaklyPointed.comp_hom,
    quillenStageGridDiagonalRealMapWeaklyPointed_hom,
    quillenStageGridToStageWeaklyPointed_hom,
    stageWeakDiagonalRealMapWeaklyPointed_hom]
  exact congrArg TopCat.Hom.hom
    (quillenStageGridToStage_realization_naturality F)

/-- Root-path compatibility for the grid-to-Q square, with the right root
cast along the source equality induced by the strict hom square. -/
def quillenStageGridToNQRootCompatibility
    (p : quillenStageGridDiagonalZeroComparisonPathData F) : Prop :=
  let left := (quillenStageGridDiagonalRealMapWeaklyPointed F p).comp
    (quillenStageGridToNQWeaklyPointed (C := D))
  let right := (quillenStageGridToNQWeaklyPointed (C := C)).comp
    (NQRealMapWeaklyPointed F)
  left.rootPath.Homotopic
    (right.rootPath.cast
      (congrArg (fun k => k (quillenStageGridDiagonalReal.basepoint C))
        (quillenStageGridToNQ_weak_square_hom F p)) rfl)

/-- Root-path compatibility for the grid-to-Stage square, with the right root
cast along the source equality induced by the strict hom square. -/
def quillenStageGridToStageRootCompatibility
    (p : quillenStageGridDiagonalZeroComparisonPathData F) : Prop :=
  let left := (quillenStageGridDiagonalRealMapWeaklyPointed F p).comp
    (quillenStageGridToStageWeaklyPointed (C := D))
  let right := (quillenStageGridToStageWeaklyPointed (C := C)).comp
    (stageWeakDiagonalRealMapWeaklyPointed C D F)
  left.rootPath.Homotopic
    (right.rootPath.cast
      (congrArg (fun k => k (quillenStageGridDiagonalReal.basepoint C))
        (quillenStageGridToStage_weak_square_hom F p)) rfl)

/-- A grid root together with its compatibility with both weakly pointed
legs of the Quillen Q/S zigzag. -/
structure QuillenStageGridZeroComparisonCoherence where
  /-- The original grid zero-comparison root, with its full original path. -/
  rootPath : quillenStageGridDiagonalZeroComparisonPathData F
  toNQ : quillenStageGridToNQRootCompatibility F rootPath
  toStage : quillenStageGridToStageRootCompatibility F rootPath

namespace QuillenStageGridZeroComparisonCoherence.Internal

theorem quillenStageGridZeroComparison_trans_cast_refl_homotopic
    {X : Type w} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (h : b = c) :
    (p.trans ((Path.refl c).cast h rfl)).Homotopic
      (p.cast rfl h.symm) := by
  cases h
  simpa using Path.Homotopic.trans_refl p

theorem quillenStageGridZeroComparison_cast_refl_trans_homotopic
    {X : Type w} [TopologicalSpace X] {a b c : X}
    (h : a = b) (p : Path b c) :
    (((Path.refl b).cast h rfl).trans p).Homotopic
      (p.cast h rfl) := by
  cases h
  simpa using Path.Homotopic.refl_trans p

theorem quillenStageGridZeroComparison_map_cast_refl
    {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y)) {a b : X} (h : a = b) :
    ((Path.refl b).cast h rfl).map g.continuous =
      (Path.refl (g b)).cast (congrArg g h) rfl := by
  cases h
  rfl

theorem quillenStageGridZeroComparison_realizedEdgePath_map_apply_of_edge_eq
    {X Y : SSet.{w}} (f : X ⟶ Y)
    {x₀ x₁ : X.obj (op ⦋0⦌)} (e : X.Edge x₀ x₁)
    {y₀ y₁ : Y.obj (op ⦋0⦌)} (e' : Y.Edge y₀ y₁)
    (h : e'.edge = (e.map f).edge) (t : unitInterval) :
    (SSet.toTop.map f).hom
        ((TopCat.pathEquiv (SSet.realizedEdgePath e)) t) =
      (TopCat.pathEquiv (SSet.realizedEdgePath e')) t := by
  have hNat := SSet.realizedEdgePath_naturality_hom f e
  have hHom : (SSet.realizedEdgePath e').hom =
      (SSet.realizedEdgePath (e.map f)).hom := by
    rw [SSet.realizedEdgePath_hom, SSet.realizedEdgePath_hom, h]
  change (SSet.toTop.map f).hom
      ((SSet.realizedEdgePath e).hom.hom (TopCat.I.homeomorph.symm t)) =
    (SSet.realizedEdgePath e').hom.hom (TopCat.I.homeomorph.symm t)
  rw [hHom, hNat]
  rfl

/-- The actual Q projection of the original grid root, with its original endpoint casts. -/
noncomputable def quillenStageGridZeroComparisonQProjectionRootPath :
    Path (NQReal.map F (NQReal.basepoint C)) (NQReal.basepoint D) :=
  (quillenStageGridZeroComparisonQProjectionPath F).cast
    (NQReal.map_basepoint_eq_realizedVertex F)
    (NQReal.basepoint_eq_realizedVertex D)

theorem quillenStageGridZeroComparisonQProjectionRootPath_homotopic :
    (quillenStageGridZeroComparisonQProjectionRootPath F).Homotopic
      (NQKSpace.zeroComparisonRootPath C D F) := by
  have h := (quillenStageGridZeroComparisonQProjectionPath_homotopic_zeroComparison F).pathCast
    (NQReal.map_basepoint_eq_realizedVertex F)
    (NQReal.basepoint_eq_realizedVertex D)
  simpa only [quillenStageGridZeroComparisonQProjectionRootPath, NQKSpace.zeroComparisonRootPath,
    NQReal.zeroComparisonPath, TopCat.Path.pathEquiv_cast] using h

theorem quillenStageGridZeroComparison_map_toNQ_source_eq :
    (SSet.toTop.map (quillenStageGridToNQ (C := D))).hom
        (quillenStageGridDiagonalRealMap F
          (quillenStageGridDiagonalReal.basepoint C)) =
      NQReal.map F (NQReal.basepoint C) := by
  have h := congrArg
    (fun k => k (quillenStageGridDiagonalReal.basepoint C))
      (quillenStageGridToNQ_realization_naturality_weak_hom F)
  simpa only [TopCat.hom_comp, ContinuousMap.comp_apply,
    NQRealMapWeaklyPointed_hom,
    quillenStageGridToNQ_map_basepoint] using h

theorem quillenStageGridZeroComparison_map_toNQ_target_eq :
    (SSet.toTop.map (quillenStageGridToNQ (C := D))).hom
        (quillenStageGridDiagonalReal.basepoint D) =
      NQReal.basepoint D :=
  quillenStageGridToNQ_map_basepoint (C := D)

theorem quillenStageGridDiagonalZeroComparisonRootPath_map_toNQ :
    ((quillenStageGridDiagonalZeroComparisonRootPath F).map
      (map_continuous
        (SSet.toTop.map (quillenStageGridToNQ (C := D))).hom)).cast
          (quillenStageGridZeroComparison_map_toNQ_source_eq F).symm
          (quillenStageGridZeroComparison_map_toNQ_target_eq (D := D)).symm =
      quillenStageGridZeroComparisonQProjectionRootPath F := by
  apply Path.ext
  ext t
  simp only [Path.map_coe, Path.cast_coe, Function.comp_apply,
    quillenStageGridDiagonalZeroComparisonRootPath,
    quillenStageGridZeroComparisonQProjectionRootPath]
  simp only [quillenStageGridDiagonalZeroComparisonRawPath,
    quillenStageGridZeroComparisonQProjectionPath, Path.trans_apply]
  split_ifs
  all_goals
    apply quillenStageGridZeroComparison_realizedEdgePath_map_apply_of_edge_eq
    rfl

/-- The actual Stage projection of the original grid root, with its original endpoint casts. -/
noncomputable def quillenStageGridZeroComparisonStageProjectionRootPath :
    Path
      ((stageWeakDiagonalReal.map C D F)
        (stageWeakDiagonalReal.basepoint C))
      (stageWeakDiagonalReal.basepoint D) :=
  (quillenStageGridZeroComparisonStageProjectionPath F).cast
    (stageWeakDiagonalLevelZeroMapped_basepoint C D F)
    (stageWeakDiagonalReal.basepoint_eq_realizedVertex D)

theorem quillenStageGridZeroComparisonStageProjectionRootPath_homotopic :
    (quillenStageGridZeroComparisonStageProjectionRootPath F).Homotopic
      (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F) := by
  have h := (quillenStageGridZeroComparisonStageProjectionPath_homotopic_levelZero F).pathCast
    (stageWeakDiagonalLevelZeroMapped_basepoint C D F)
    (stageWeakDiagonalReal.basepoint_eq_realizedVertex D)
  simpa only [quillenStageGridZeroComparisonStageProjectionRootPath,
    stageWeakDiagonalKSpace.zeroComparisonRootPath,
    stageWeakDiagonalLevelZeroRealizedPath] using h

theorem quillenStageGridToStage_map_basepoint (A : Type u) [Category.{v} A]
    [Preadditive A] [HasZeroObject A] [HasBinaryBiproducts A]
    [ExactCategory A] :
    (SSet.toTop.map
      (quillenStageGridToStageWeakDiagonal (C := A))).hom
        (quillenStageGridDiagonalReal.basepoint A) =
      stageWeakDiagonalReal.basepoint A := by
  rw [quillenStageGridDiagonalReal.basepoint,
    ← SSet.realizedVertex_naturality,
    quillenStageGridToStageWeakDiagonal_zeroVertex,
    ← stageWeakDiagonalReal.basepoint_eq_realizedVertex]

theorem quillenStageGridToStageWeaklyPointed_rootPath_homotopic_refl
    (A : Type u) [Category.{v} A] [Preadditive A]
    [HasZeroObject A] [HasBinaryBiproducts A] [ExactCategory A] :
    (quillenStageGridToStageWeaklyPointed (C := A)).rootPath.Homotopic
      ((Path.refl (stageWeakDiagonalReal.basepoint A)).cast
        (by
          rw [quillenStageGridToStageWeaklyPointed_hom]
          exact quillenStageGridToStage_map_basepoint A) rfl) := by
  let g := (outerEdgewiseStageDiagonalComparisonWeaklyPointed (C := A)).hom
  let h1 := quillenStageGridStageProjection_map_basepoint (C := A)
  let h2 := outerEdgewiseStageDiagonalComparison_map_basepoint (C := A)
  let hWeak : (quillenStageGridToStageWeaklyPointed (C := A)).hom
      (quillenStageGridDiagonalReal.basepoint A) =
        stageWeakDiagonalReal.basepoint A := by
    rw [quillenStageGridToStageWeaklyPointed_hom]
    exact quillenStageGridToStage_map_basepoint A
  change ((((Path.refl (edgewiseStageWeakDiagonalReal.basepoint A)).cast
      h1 rfl).map g.continuous).trans
        ((Path.refl (stageWeakDiagonalReal.basepoint A)).cast h2 rfl)).Homotopic
      ((Path.refl (stageWeakDiagonalReal.basepoint A)).cast hWeak rfl)
  rw [quillenStageGridZeroComparison_map_cast_refl]
  have h := quillenStageGridZeroComparison_cast_refl_trans_homotopic (congrArg g h1)
    ((Path.refl (stageWeakDiagonalReal.basepoint A)).cast h2 rfl)
  convert h using 1
  all_goals
    apply Path.ext
    rfl

theorem quillenStageGridZeroComparison_map_toStage_source_eq :
    (SSet.toTop.map
      (quillenStageGridToStageWeakDiagonal (C := D))).hom
        (quillenStageGridDiagonalRealMap F
          (quillenStageGridDiagonalReal.basepoint C)) =
      (stageWeakDiagonalReal.map C D F).hom
        (stageWeakDiagonalReal.basepoint C) := by
  have h := congrArg
    (fun k => k (quillenStageGridDiagonalReal.basepoint C))
      (quillenStageGridToStage_weak_square_hom F (quillenStageGridDiagonalZeroComparisonRootPath F))
  simpa only [ContinuousMap.WeaklyPointed.comp_hom,
    ContinuousMap.comp_apply,
    quillenStageGridDiagonalRealMapWeaklyPointed_hom,
    quillenStageGridToStageWeaklyPointed_hom,
    stageWeakDiagonalRealMapWeaklyPointed_hom,
    quillenStageGridToStage_map_basepoint] using h

theorem quillenStageGridZeroComparison_map_toStage_target_eq :
    (SSet.toTop.map
      (quillenStageGridToStageWeakDiagonal (C := D))).hom
        (quillenStageGridDiagonalReal.basepoint D) =
      stageWeakDiagonalReal.basepoint D :=
  quillenStageGridToStage_map_basepoint D

theorem quillenStageGridDiagonalZeroComparisonRootPath_map_toStage :
    ((quillenStageGridDiagonalZeroComparisonRootPath F).map
      (map_continuous
        (SSet.toTop.map
          (quillenStageGridToStageWeakDiagonal (C := D))).hom)).cast
            (quillenStageGridZeroComparison_map_toStage_source_eq F).symm
            (quillenStageGridZeroComparison_map_toStage_target_eq (D := D)).symm =
      quillenStageGridZeroComparisonStageProjectionRootPath F := by
  apply Path.ext
  ext t
  simp only [Path.map_coe, Path.cast_coe, Function.comp_apply,
    quillenStageGridDiagonalZeroComparisonRootPath,
    quillenStageGridZeroComparisonStageProjectionRootPath]
  simp only [quillenStageGridDiagonalZeroComparisonRawPath,
    quillenStageGridZeroComparisonStageProjectionPath, Path.trans_apply]
  split_ifs
  all_goals
    apply quillenStageGridZeroComparison_realizedEdgePath_map_apply_of_edge_eq
    rfl

end QuillenStageGridZeroComparisonCoherence.Internal

/-- The canonical grid root is compatible with the weakly pointed Q leg. -/
theorem quillenStageGridDiagonalZeroComparisonRootPath_toNQ :
    quillenStageGridToNQRootCompatibility F
      (quillenStageGridDiagonalZeroComparisonRootPath F) := by
  unfold quillenStageGridToNQRootCompatibility
  dsimp only [ContinuousMap.WeaklyPointed.comp_rootPath]
  let pMap := (quillenStageGridDiagonalZeroComparisonRootPath F).map
    (quillenStageGridToNQWeaklyPointed (C := D)).hom.continuous
  let hTgt := quillenStageGridZeroComparison_map_toNQ_target_eq (D := D)
  let hC := quillenStageGridToNQ_map_basepoint (C := C)
  let qRoot := NQKSpace.zeroComparisonRootPath C D F
  let g := (NQRealMapWeaklyPointed F).hom
  let hSrc := quillenStageGridZeroComparison_map_toNQ_source_eq F
  let hSquare := congrArg
    (fun k => k (quillenStageGridDiagonalReal.basepoint C))
      (quillenStageGridToNQ_weak_square_hom F (quillenStageGridDiagonalZeroComparisonRootPath F))
  change (pMap.trans ((Path.refl (NQReal.basepoint D)).cast hTgt rfl)).Homotopic
    (((((Path.refl (NQReal.basepoint C)).cast hC rfl).map g.continuous).trans
      qRoot).cast hSquare rfl)
  have hLeft := quillenStageGridZeroComparison_trans_cast_refl_homotopic pMap hTgt
  have hNorm : pMap.cast rfl hTgt.symm =
      (quillenStageGridZeroComparisonQProjectionRootPath F).cast hSrc rfl := by
    rw [← quillenStageGridDiagonalZeroComparisonRootPath_map_toNQ F]
    apply Path.ext
    rfl
  rw [hNorm] at hLeft
  have hQ := (quillenStageGridZeroComparisonQProjectionRootPath_homotopic F).pathCast hSrc rfl
  have hLeftFinal := hLeft.trans hQ
  have hMapRefl := quillenStageGridZeroComparison_map_cast_refl g hC
  rw [hMapRefl]
  have hRight := quillenStageGridZeroComparison_cast_refl_trans_homotopic (congrArg g hC) qRoot
  have hRightCast := hRight.pathCast hSquare rfl
  have hRightEq :
      (qRoot.cast (congrArg g hC) rfl).cast hSquare rfl =
        qRoot.cast hSrc rfl := by
    apply Path.ext
    rfl
  have hRightFinal :
      ((((Path.refl (g (NQReal.basepoint C))).cast
          (congrArg g hC) rfl).trans qRoot).cast hSquare rfl).Homotopic
        (qRoot.cast hSrc rfl) := by
    convert hRightCast using 1
    exact hRightEq
  exact hLeftFinal.trans hRightFinal.symm

/-- The canonical grid root is compatible with the factored weakly pointed
Stage leg. -/
theorem quillenStageGridDiagonalZeroComparisonRootPath_toStage :
    quillenStageGridToStageRootCompatibility F
      (quillenStageGridDiagonalZeroComparisonRootPath F) := by
  unfold quillenStageGridToStageRootCompatibility
  dsimp only [ContinuousMap.WeaklyPointed.comp_rootPath]
  let pMap := (quillenStageGridDiagonalZeroComparisonRootPath F).map
    (quillenStageGridToStageWeaklyPointed (C := D)).hom.continuous
  let hTgt : (quillenStageGridToStageWeaklyPointed (C := D)).hom
      (quillenStageGridDiagonalReal.basepoint D) =
        stageWeakDiagonalReal.basepoint D := by
    rw [quillenStageGridToStageWeaklyPointed_hom]
    exact quillenStageGridZeroComparison_map_toStage_target_eq (D := D)
  let hC : (quillenStageGridToStageWeaklyPointed (C := C)).hom
      (quillenStageGridDiagonalReal.basepoint C) =
        stageWeakDiagonalReal.basepoint C := by
    rw [quillenStageGridToStageWeaklyPointed_hom]
    exact quillenStageGridToStage_map_basepoint C
  let sRoot := stageWeakDiagonalKSpace.zeroComparisonRootPath C D F
  let g := (stageWeakDiagonalRealMapWeaklyPointed C D F).hom
  let hSrc : (quillenStageGridToStageWeaklyPointed (C := D)).hom
      (quillenStageGridDiagonalRealMap F
        (quillenStageGridDiagonalReal.basepoint C)) =
      (stageWeakDiagonalReal.map C D F).hom
        (stageWeakDiagonalReal.basepoint C) := by
    rw [quillenStageGridToStageWeaklyPointed_hom]
    exact quillenStageGridZeroComparison_map_toStage_source_eq F
  let hSquare := congrArg
    (fun k => k (quillenStageGridDiagonalReal.basepoint C))
      (quillenStageGridToStage_weak_square_hom F (quillenStageGridDiagonalZeroComparisonRootPath F))
  have hTail := quillenStageGridToStageWeaklyPointed_rootPath_homotopic_refl D
  have hLeftReplace := (Path.Homotopic.refl pMap).hcomp hTail
  have hLeftNorm := quillenStageGridZeroComparison_trans_cast_refl_homotopic pMap hTgt
  have hLeft :
      (pMap.trans
        (quillenStageGridToStageWeaklyPointed (C := D)).rootPath).Homotopic
        (pMap.cast rfl hTgt.symm) := by
    refine hLeftReplace.trans ?_
    convert hLeftNorm using 1
  have hNorm : pMap.cast rfl hTgt.symm =
      (quillenStageGridZeroComparisonStageProjectionRootPath F).cast hSrc rfl := by
    apply Path.ext
    ext t
    simp only [pMap, Path.cast_coe, Path.map_coe, Function.comp_apply]
    rw [quillenStageGridToStageWeaklyPointed_hom]
    have hm := congrArg (fun p => p t)
      (quillenStageGridDiagonalZeroComparisonRootPath_map_toStage F)
    change (SSet.toTop.map
      (quillenStageGridToStageWeakDiagonal (C := D))).hom
        ((quillenStageGridDiagonalZeroComparisonRootPath F) t) =
      (quillenStageGridZeroComparisonStageProjectionRootPath F) t at hm
    exact hm
  rw [hNorm] at hLeft
  have hS := (quillenStageGridZeroComparisonStageProjectionRootPath_homotopic F).pathCast hSrc rfl
  have hLeftFinal := hLeft.trans hS
  have hHead := quillenStageGridToStageWeaklyPointed_rootPath_homotopic_refl C
  have hHeadMap := Path.Homotopic.map hHead g
  have hRightReplace := hHeadMap.hcomp (Path.Homotopic.refl sRoot)
  have hMapRefl := quillenStageGridZeroComparison_map_cast_refl g hC
  rw [hMapRefl] at hRightReplace
  have hRightNorm := quillenStageGridZeroComparison_cast_refl_trans_homotopic (congrArg g hC) sRoot
  have hRight := hRightReplace.trans hRightNorm
  have hRightCast := hRight.pathCast hSquare rfl
  have hRightEq :
      (sRoot.cast (congrArg g hC) rfl).cast hSquare rfl =
        sRoot.cast hSrc rfl := by
    apply Path.ext
    rfl
  have hRightFinal :
      ((((quillenStageGridToStageWeaklyPointed (C := C)).rootPath.map
          g.continuous).trans sRoot).cast hSquare rfl).Homotopic
        (sRoot.cast hSrc rfl) := by
    convert hRightCast using 1
    exact hRightEq
  exact hLeftFinal.trans hRightFinal.symm

/-- Canonical Stage-grid zero-comparison coherence for an additive exact
functor. -/
noncomputable def quillenStageGridZeroComparisonCoherence :
    QuillenStageGridZeroComparisonCoherence F where
  rootPath := quillenStageGridDiagonalZeroComparisonRootPath F
  toNQ := quillenStageGridDiagonalZeroComparisonRootPath_toNQ F
  toStage := quillenStageGridDiagonalZeroComparisonRootPath_toStage F

section

-- Preserve the original qualified predicates for the same root compatibility data.
open AlgebraicKTheory renaming
  quillenStageGridToNQRootCompatibility → quillenStageGridToNQ_rootCompatibility,
  quillenStageGridToStageRootCompatibility → quillenStageGridToStage_rootCompatibility
export _root_ (quillenStageGridToNQ_rootCompatibility quillenStageGridToStage_rootCompatibility)

end

end AlgebraicKTheory

end
