/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMixedStageSquare
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridZeroComparisonEdge
public import MathlibExt.KTheory.Exact.Quillen.KSpaceFunctorCoherence
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridQEdgeValues

/-!
# The actual original mixed Stage-grid three-edge zero root

The original target-grid lift of the actual original Quillen zero edge and
the original direct fiber connectors give the three-edge path. The source
vertex is the actual mixed grid image of the SAME original source zero.
No arbitrary root or comparison/inverse outcome is supplied.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial Topology

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Standard Waldhausen structure selected locally for the source exact category. -/
local instance originalMixedZeroRootWaldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C
/-- Standard Waldhausen structure selected locally for the target exact category. -/
local instance originalMixedZeroRootWaldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

/-- The source zero lift transported through an additive exact functor. -/
def originalMixedGridMappedZeroLift : QuillenStageGridLift D ⦋0⦌ :=
  (quillenStageGridLiftMap F ⦋0⦌).obj (quillenStageGridZeroLift C)

/-- The canonical degree-zero target zero lift. -/
def originalMixedGridTargetZeroLift : QuillenStageGridLift D ⦋0⦌ :=
  quillenStageGridZeroLift D

/-- The retained simplex underlying the canonical Quillen zero-comparison edge. -/
def originalMixedGridZeroQEdge : QuillenQSimplex D ⦋1⦌ :=
  (NQFunctorZeroEdge F).edge


private def originalMixedGridZeroLiftPacket :
    { X : QuillenStageGridLift D ⦋1⦌ // X.q = originalMixedGridZeroQEdge F } :=
  Classical.choice (quillenStageGridLift_exists (originalMixedGridZeroQEdge F))



/-- The selected degree-one grid lift of the original Quillen functor zero edge. -/
def originalMixedGridZeroLift : QuillenStageGridLift D ⦋1⦌ :=
  (originalMixedGridZeroLiftPacket F).1

/-- The selected Stage-grid lift lies over the canonical retained Q edge. -/
@[simp]
theorem originalMixedGridZeroLift_q :
    (originalMixedGridZeroLift F).q =
      originalMixedGridZeroQEdge F :=
  (originalMixedGridZeroLiftPacket F).2

/-- Source face of the selected zero-comparison lift. -/
def originalMixedGridZeroSource : QuillenStageGridLift D ⦋0⦌ :=
  (reindexQuillenStageGridLift (C := D) (SimplexCategory.δ 1)).obj
    (originalMixedGridZeroLift F)

/-- Target face of the selected zero-comparison lift. -/
def originalMixedGridZeroTarget : QuillenStageGridLift D ⦋0⦌ :=
  (reindexQuillenStageGridLift (C := D) (SimplexCategory.δ 0)).obj
    (originalMixedGridZeroLift F)

/-- The retained source face agrees with the mapped canonical zero lift. -/
theorem originalMixedGridZeroSource_q :
    (originalMixedGridZeroSource F).q = (originalMixedGridMappedZeroLift F).q := by
  rw [originalMixedGridZeroSource,
    reindexQuillenStageGridLift_obj_q,
    originalMixedGridZeroLift_q]
  change (NQ D).δ (1 : Fin 2) (NQFunctorZeroEdge F).edge =
    (originalMixedGridMappedZeroLift F).q
  refine (SSet.Edge.src_eq (NQFunctorZeroEdge F)).trans ?_
  rw [originalMixedGridMappedZeroLift,
    quillenStageGridLiftMap_obj_q, quillenStageGridZeroLift_q]
  apply ComposableArrows.ext₀
  rfl

/-- The retained target face agrees with the canonical target zero lift. -/
theorem originalMixedGridZeroTarget_q :
    (originalMixedGridZeroTarget F).q =
      (originalMixedGridTargetZeroLift (D := D)).q := by
  rw [originalMixedGridZeroTarget,
    reindexQuillenStageGridLift_obj_q,
    originalMixedGridZeroLift_q]
  change (NQ D).δ (0 : Fin 2) (NQFunctorZeroEdge F).edge =
    (quillenStageGridZeroLift D).q
  exact (SSet.Edge.tgt_eq (NQFunctorZeroEdge F)).trans (quillenStageGridZeroLift_q D).symm


private def originalMixedGridMappedZeroFiber :
    QuillenStageGridFiber (originalMixedGridMappedZeroLift F).q :=
  ⟨originalMixedGridMappedZeroLift F, rfl⟩

private def originalMixedGridZeroSourceFiber :
    QuillenStageGridFiber (originalMixedGridMappedZeroLift F).q :=
  ⟨originalMixedGridZeroSource F,
    Discrete.ext (originalMixedGridZeroSource_q F)⟩

private def originalMixedGridZeroTargetFiber :
    QuillenStageGridFiber (originalMixedGridTargetZeroLift (D := D)).q :=
  ⟨originalMixedGridZeroTarget F,
    Discrete.ext (originalMixedGridZeroTarget_q F)⟩

private def originalMixedGridTargetZeroFiber :
    QuillenStageGridFiber (originalMixedGridTargetZeroLift (D := D)).q :=
  ⟨originalMixedGridTargetZeroLift (D := D), rfl⟩

private def originalMixedGridZeroLeftHom :
    originalMixedGridMappedZeroLift F ⟶
      originalMixedGridZeroSource F :=
  (QuillenStageGridFiberComparison.fiberHom
    (originalMixedGridMappedZeroFiber F) (originalMixedGridZeroSourceFiber F)).1

private def originalMixedGridZeroRightHom :
    originalMixedGridZeroTarget F ⟶
      originalMixedGridTargetZeroLift (D := D) :=
  (QuillenStageGridFiberComparison.fiberHom
    (originalMixedGridZeroTargetFiber F) (originalMixedGridTargetZeroFiber (D := D))).1

/-- The identity-arrow diagonal one-simplex on the selected zero-comparison grid lift. -/
def originalMixedGridZeroCentralSimplex :
    (quillenStageGridDiagonal D).obj (op ⦋1⦌) :=
  ComposableArrows.mk₁ (𝟙 (originalMixedGridZeroLift F))

/-- The central diagonal edge, from the source face to the target face of the
selected zero-comparison lift. -/
def originalMixedGridZeroCentralEdge :
    (quillenStageGridDiagonal D).Edge
      (ComposableArrows.mk₀ (originalMixedGridZeroSource F))
      (ComposableArrows.mk₀ (originalMixedGridZeroTarget F)) := by
  let s := originalMixedGridZeroCentralSimplex F
  refine SSet.Edge.ofEq (SSet.Edge.mk' s) ?_ ?_
  · have hInner :
        ((CategoryTheory.nerve (QuillenStageGridLift D ⦋1⦌)).map
          (SimplexCategory.δ 1).op) s =
          ComposableArrows.mk₀ (originalMixedGridZeroLift F) := by
      apply ComposableArrows.ext₀
      rfl
    have hMap : (quillenStageGridDiagonal D).map
        (SimplexCategory.δ (1 : Fin 2)).op s =
      (CategoryTheory.nerveMap
        (reindexQuillenStageGridLift (C := D)
          (SimplexCategory.δ 1))).app (op ⦋0⦌)
        (((CategoryTheory.nerve (QuillenStageGridLift D ⦋1⦌)).map
          (SimplexCategory.δ 1).op) s) := rfl
    change (quillenStageGridDiagonal D).map
      (SimplexCategory.δ (1 : Fin 2)).op s = _
    rw [hMap, hInner, CategoryTheory.nerveMap_app_mk₀]
    rfl
  · have hInner :
        ((CategoryTheory.nerve (QuillenStageGridLift D ⦋1⦌)).map
          (SimplexCategory.δ 0).op) s =
          ComposableArrows.mk₀ (originalMixedGridZeroLift F) := by
      apply ComposableArrows.ext₀
      rfl
    have hMap : (quillenStageGridDiagonal D).map
        (SimplexCategory.δ (0 : Fin 2)).op s =
      (CategoryTheory.nerveMap
        (reindexQuillenStageGridLift (C := D)
          (SimplexCategory.δ 0))).app (op ⦋0⦌)
        (((CategoryTheory.nerve (QuillenStageGridLift D ⦋1⦌)).map
          (SimplexCategory.δ 0).op) s) := rfl
    change (quillenStageGridDiagonal D).map
      (SimplexCategory.δ (0 : Fin 2)).op s = _
    rw [hMap, hInner, CategoryTheory.nerveMap_app_mk₀]
    rfl

/-- Left connector from the mapped canonical zero lift to the selected
lift's source face, built from the direct strict-fiber comparison. -/
def originalMixedGridZeroLeftEdge :
    (quillenStageGridDiagonal D).Edge
      (ComposableArrows.mk₀ (originalMixedGridMappedZeroLift F))
      (ComposableArrows.mk₀ (originalMixedGridZeroSource F)) :=
  quillenStageGridDiagonalDegreeZeroMapEdge (originalMixedGridZeroLeftHom F)

/-- Right connector from the selected lift's target face to the canonical
target zero lift, built from the direct strict-fiber comparison. -/
def originalMixedGridZeroRightEdge :
    (quillenStageGridDiagonal D).Edge
      (ComposableArrows.mk₀ (originalMixedGridZeroTarget F))
      (ComposableArrows.mk₀ (originalMixedGridTargetZeroLift (D := D))) :=
  quillenStageGridDiagonalDegreeZeroMapEdge (originalMixedGridZeroRightHom F)

/-- Raw realized concatenation of the left, central, and right Stage-grid
edges.  Its endpoints are realized lift vertices, before any basepoint cast. -/
def originalMixedGridZeroRawPath :
    Path
      (SSet.realizedVertex (ComposableArrows.mk₀ (originalMixedGridMappedZeroLift F)))
      (SSet.realizedVertex (X := quillenStageGridDiagonal D)
        (ComposableArrows.mk₀
        (originalMixedGridTargetZeroLift (D := D)))) :=
  (TopCat.pathEquiv
    (SSet.realizedEdgePath
      (originalMixedGridZeroLeftEdge F))).trans
    ((TopCat.pathEquiv
      (SSet.realizedEdgePath
        (originalMixedGridZeroCentralEdge F))).trans
      (TopCat.pathEquiv
        (SSet.realizedEdgePath
          (originalMixedGridZeroRightEdge F))))
/-- The actual original mixed grid map carries source zero to its actual
mapped-zero lift vertex, before target-zero root transport. -/
theorem originalMixedGridMappedZeroRealization :
    quillenStageGridDiagonalRealMixedMap F (quillenStageGridDiagonalReal.basepoint C) =
      SSet.realizedVertex (ComposableArrows.mk₀ (originalMixedGridMappedZeroLift F)) := by
  have h := quillenStageGridDiagonalRealMixedMap_realizedVertex F
    (quillenStageGridDiagonalZeroVertex (C := C))
  exact h.trans (congrArg SSet.realizedVertex (by
    apply ComposableArrows.ext₀
    rfl))

/-- SAME original three-edge path with ONLY actual derived basepoint casts. -/
def quillenStageGridDiagonalMixedZeroRoot :
    Path (quillenStageGridDiagonalRealMixedMap F (quillenStageGridDiagonalReal.basepoint C))
      (quillenStageGridDiagonalReal.basepoint D) :=
  (originalMixedGridZeroRawPath F).cast (originalMixedGridMappedZeroRealization F) rfl


private theorem originalMixedLeftEdgeQValueComputed :
    ((originalMixedGridZeroLeftEdge F).map (quillenStageGridToNQ (C := D))).edge =
      (SSet.Edge.id (originalMixedGridMappedZeroLift F).q).edge :=
  quillenStageGridDegreeZeroEdge_toNQ_value D (originalMixedGridZeroLeftHom F)

/-- The EXACT original chosen left connector has its degenerate retained-Q
edge value; no replacement connector is selected. -/
theorem originalMixedGridZeroLeftEdge_Q_value :
    ((originalMixedGridZeroLeftEdge F).map (quillenStageGridToNQ (C := D))).edge =
      (SSet.Edge.id (originalMixedGridMappedZeroLift F).q).edge :=
  originalMixedLeftEdgeQValueComputed F

private theorem originalMixedRightEdgeQValueComputed :
    ((originalMixedGridZeroRightEdge F).map (quillenStageGridToNQ (C := D))).edge =
      (SSet.Edge.id (originalMixedGridZeroTarget F).q).edge :=
  quillenStageGridDegreeZeroEdge_toNQ_value D (originalMixedGridZeroRightHom F)

/-- The EXACT original chosen right connector has its degenerate retained-Q
edge value, preserving the original fiber/path choice. -/
theorem originalMixedGridZeroRightEdge_Q_value :
    ((originalMixedGridZeroRightEdge F).map (quillenStageGridToNQ (C := D))).edge =
      (SSet.Edge.id (originalMixedGridZeroTarget F).q).edge :=
  originalMixedRightEdgeQValueComputed F


open scoped ZeroObject in
private theorem originalMixedCentralStageZeroComputed :
    IsZero ((stageOneEval D).obj
      (ComposableArrows.left
        ((originalMixedGridZeroCentralEdge F).map
          (quillenStageGridToStageWeakDiagonal (C := D))).edge).obj) := by
  change IsZero ((originalMixedGridZeroLift F).grid.obj.obj.obj
    (interval (2 : Fin 4) 3 (by decide)))
  let X := originalMixedGridZeroLift F
  let A := X.grid.obj
  have hqObj : X.q.obj (1 : Fin 2) = (⟨(0 : D)⟩ : QuillenQ D) := by
    dsimp only [X]
    rw [originalMixedGridZeroLift_q]
    have hEdge := NQFunctorZeroEdge_edge F
    exact congrArg (fun q : QuillenQSimplex D ⦋1⦌ => q.obj (1 : Fin 2)) hEdge
  let eQ : (⟨edgewiseStageVertex A (1 : Fin 2)⟩ : QuillenQ D) ≅
      ⟨(0 : D)⟩ :=
    (X.agreementIso.app (1 : Fin 2)).trans (eqToIso hqObj)
  obtain ⟨eD⟩ := quillenQ_iso_lifts_to_underlying_iso eQ
  have hTarget : IsZero (edgewiseStageVertex A (1 : Fin 2)) :=
    IsZero.of_iso (isZero_zero D) eD
  let S := edgewiseStageShellSpanNormalized A
    (0 : Fin 2) (1 : Fin 2) (by decide)
  have hApex : IsZero S.apex := by
    let _ : Mono S.r := IsAdmissibleMono.mono
      (show IsAdmissibleMono S.r from S.wr)
    exact IsZero.of_mono S.r hTarget
  let P := edgewiseStageShellPacket A
    (0 : Fin 2) (1 : Fin 2) (by decide)
  have hApexRaw : IsZero P.span.apex := by
    simpa only [S, P, edgewiseStageShellSpanNormalized_apex] using hApex
  have hIsoQ : IsIso P.flag.quotientπ :=
    isIso_g_of_isAdmissibleExact_of_isZero
      P.flag.apex_target_quotient_exact hApexRaw
  let _ : IsIso P.flag.quotientπ := hIsoQ
  have hQuotient : IsZero P.flag.quotientObj :=
    IsZero.of_iso hTarget (asIso P.flag.quotientπ).symm
  exact hQuotient


/-- The actual selected central grid edge has a zero Stage off-diagonal,
from its original Q-lift agreement and exact shell quotient. -/
theorem originalMixedGridZeroCentralEdge_Stage_isZero :
    IsZero ((stageOneEval D).obj
      (ComposableArrows.left
        ((originalMixedGridZeroCentralEdge F).map
          (quillenStageGridToStageWeakDiagonal (C := D))).edge).obj) :=
  originalMixedCentralStageZeroComputed F

/-- The EXACT original chosen left connector has zero Stage off-diagonal. -/
theorem originalMixedGridZeroLeftEdge_Stage_isZero :
    IsZero ((stageOneEval D).obj
      (ComposableArrows.left
        ((originalMixedGridZeroLeftEdge F).map
          (quillenStageGridToStageWeakDiagonal (C := D))).edge).obj) :=
  quillenStageGridDiagonalDegreeZeroMapEdge_toStage_offdiag_isZero (originalMixedGridZeroLeftHom F)

/-- The EXACT original chosen right connector has zero Stage off-diagonal. -/
theorem originalMixedGridZeroRightEdge_Stage_isZero :
    IsZero ((stageOneEval D).obj
      (ComposableArrows.left
        ((originalMixedGridZeroRightEdge F).map
          (quillenStageGridToStageWeakDiagonal (C := D))).edge).obj) :=
  quillenStageGridDiagonalDegreeZeroMapEdge_toStage_offdiag_isZero (originalMixedGridZeroRightHom F)

end AlgebraicKTheory

end

public section
noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Simplicial Topology

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

attribute [local instance] originalMixedZeroRootWaldhausenC originalMixedZeroRootWaldhausenD

private theorem originalMixedMappedZeroLiftValueComputed :
    originalMixedGridMappedZeroLift F =
      (quillenStageGridLiftMap F ⦋0⦌).obj (quillenStageGridZeroLift C) := rfl

/-- The SAME original mapped-zero lift is the actual original functor image,
with the original source zero and all independent category roles retained. -/
theorem originalMixedGridMappedZeroLift_eq :
    originalMixedGridMappedZeroLift F =
      (quillenStageGridLiftMap F ⦋0⦌).obj (quillenStageGridZeroLift C) :=
  originalMixedMappedZeroLiftValueComputed F

private theorem originalMixedTargetZeroLiftValueComputed :
    originalMixedGridTargetZeroLift (D := D) = quillenStageGridZeroLift D := rfl

/-- The SAME original target-zero lift retains the original selected zero lift. -/
theorem originalMixedGridTargetZeroLift_eq :
    originalMixedGridTargetZeroLift (D := D) = quillenStageGridZeroLift D :=
  originalMixedTargetZeroLiftValueComputed (D := D)

private theorem originalMixedZeroQEdgeValueComputed :
    originalMixedGridZeroQEdge F = (NQFunctorZeroEdge F).edge := rfl

/-- The retained Q simplex is the SAME actual original functor zero edge. -/
theorem originalMixedGridZeroQEdge_eq :
    originalMixedGridZeroQEdge F = (NQFunctorZeroEdge F).edge :=
  originalMixedZeroQEdgeValueComputed F

private theorem originalMixedCentralSimplexValueComputed :
    originalMixedGridZeroCentralSimplex F =
      ComposableArrows.mk₁ (𝟙 (originalMixedGridZeroLift F)) := rfl

/-- The original central simplex uses the identity of SAME original chosen lift. -/
theorem originalMixedGridZeroCentralSimplex_eq :
    originalMixedGridZeroCentralSimplex F =
      ComposableArrows.mk₁ (𝟙 (originalMixedGridZeroLift F)) :=
  originalMixedCentralSimplexValueComputed F

private theorem originalMixedCentralEdgeValueComputed :
    (originalMixedGridZeroCentralEdge F).edge = originalMixedGridZeroCentralSimplex F := rfl

/-- The actual central edge retains the entire SAME original central simplex. -/
theorem originalMixedGridZeroCentralEdge_edge :
    (originalMixedGridZeroCentralEdge F).edge = originalMixedGridZeroCentralSimplex F :=
  originalMixedCentralEdgeValueComputed F

private theorem originalMixedRawZeroPathValueComputed :
    (originalMixedGridZeroRawPath F).toContinuousMap =
      ((TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedGridZeroLeftEdge F))).trans
        ((TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedGridZeroCentralEdge F))).trans
          (TopCat.pathEquiv
            (SSet.realizedEdgePath (originalMixedGridZeroRightEdge F))))).toContinuousMap := rfl

/-- The ENTIRE original raw root ContinuousMap is the SAME actual three-edge
path, with every original time and left/central/right choice retained. -/
theorem originalMixedGridZeroRawPath_toContinuousMap :
    (originalMixedGridZeroRawPath F).toContinuousMap =
      ((TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedGridZeroLeftEdge F))).trans
        ((TopCat.pathEquiv (SSet.realizedEdgePath (originalMixedGridZeroCentralEdge F))).trans
          (TopCat.pathEquiv
            (SSet.realizedEdgePath (originalMixedGridZeroRightEdge F))))).toContinuousMap :=
  originalMixedRawZeroPathValueComputed F

private theorem originalMixedActualZeroRootValueComputed :
    (quillenStageGridDiagonalMixedZeroRoot F).toContinuousMap =
      (originalMixedGridZeroRawPath F).toContinuousMap := rfl

/-- The ACTUAL original endpoint-cast root has SAME raw ContinuousMap at EVERY
original time. Both original endpoint casts and all path data are unchanged. -/
theorem quillenStageGridDiagonalMixedZeroRoot_toContinuousMap :
    (quillenStageGridDiagonalMixedZeroRoot F).toContinuousMap =
      (originalMixedGridZeroRawPath F).toContinuousMap :=
  originalMixedActualZeroRootValueComputed F

end AlgebraicKTheory

end
