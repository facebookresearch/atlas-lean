/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridFiberConnected
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMapReindex
public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzagNaturality
public import MathlibExt.KTheory.Exact.Quillen.ZeroCoherence
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroEdge
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalZeroEdgeRealization

/-!
# The explicit Stage-grid zero-comparison edge chain

For an additive exact functor, this file chooses a Stage-grid lift of the
canonical Quillen zero-comparison edge.  Direct strict-fiber morphisms join
its two faces to the canonical source and target zero lifts, producing three
explicit diagonal edges.  Their Q projections are respectively the identity,
the canonical zero-comparison edge, and the identity.  Their Stage projections
have zero off-diagonal component and telescope in the realized fundamental
groupoid to the canonical level-zero edge.

Only the raw edge chain and its projection homotopies are constructed here.
There is no endpoint cast to the chosen realization basepoints, weakly pointed
map, root-compatibility structure, loop naturality, weak equivalence, group
comparison, direct Q/S equivalence, or spectrum map.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial ZeroObject
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial Topology

universe v u

namespace AlgebraicKTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

local instance waldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

local instance waldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

/-- The canonical degree-zero Stage-grid lift of the zero Stage. -/
noncomputable def quillenStageGridZeroLift (E : Type u) [Category.{v} E]
    [Preadditive E] [HasZeroObject E] [HasBinaryBiproducts E]
    [ExactCategory E] : QuillenStageGridLift E ⦋0⦌ :=
  QuillenStageGridLift.ofGrid
    (⟨⟨zeroDiagram E 1, isStage_zeroDiagram E 1⟩⟩ :
      StageWeakCategory E 1)

/-- The source zero lift transported through an additive exact functor. -/
noncomputable def quillenStageGridMappedZeroLift : QuillenStageGridLift D ⦋0⦌ :=
  (quillenStageGridLiftMap F ⦋0⦌).obj (quillenStageGridZeroLift C)

/-- The canonical degree-zero target zero lift. -/
noncomputable def quillenStageGridTargetZeroLift : QuillenStageGridLift D ⦋0⦌ :=
  quillenStageGridZeroLift D

/-- The retained simplex underlying the canonical Quillen zero-comparison edge. -/
noncomputable def quillenStageGridZeroComparisonQEdge : QuillenQSimplex D ⦋1⦌ :=
  (NQ.zeroComparisonEdge F).edge

namespace QuillenStageGridZeroComparisonEdge.Internal

@[no_expose]
noncomputable def quillenStageGridZeroComparisonLiftPacket :
    { X : QuillenStageGridLift D ⦋1⦌ // X.q = quillenStageGridZeroComparisonQEdge F } :=
  Classical.choice (quillenStageGridLift_exists (quillenStageGridZeroComparisonQEdge F))

end QuillenStageGridZeroComparisonEdge.Internal

open QuillenStageGridZeroComparisonEdge.Internal

noncomputable def quillenStageGridZeroComparisonLift : QuillenStageGridLift D ⦋1⦌ :=
  (quillenStageGridZeroComparisonLiftPacket F).1

/-- The selected Stage-grid lift lies over the canonical retained Q edge. -/
@[simp]
theorem quillenStageGridZeroComparisonLift_q :
    (quillenStageGridZeroComparisonLift F).q =
      quillenStageGridZeroComparisonQEdge F :=
  (quillenStageGridZeroComparisonLiftPacket F).2

/-- Source face of the selected zero-comparison lift. -/
noncomputable def quillenStageGridZeroComparisonLiftSource : QuillenStageGridLift D ⦋0⦌ :=
  (reindexQuillenStageGridLift (C := D) (SimplexCategory.δ 1)).obj
    (quillenStageGridZeroComparisonLift F)

/-- Target face of the selected zero-comparison lift. -/
noncomputable def quillenStageGridZeroComparisonLiftTarget : QuillenStageGridLift D ⦋0⦌ :=
  (reindexQuillenStageGridLift (C := D) (SimplexCategory.δ 0)).obj
    (quillenStageGridZeroComparisonLift F)

/-- The retained source face agrees with the mapped canonical zero lift. -/
theorem quillenStageGridZeroComparisonLiftSource_q :
    (quillenStageGridZeroComparisonLiftSource F).q = (quillenStageGridMappedZeroLift F).q := by
  rw [quillenStageGridZeroComparisonLiftSource,
    reindexQuillenStageGridLift_obj_q,
    quillenStageGridZeroComparisonLift_q]
  apply ComposableArrows.ext₀
  rfl

/-- The retained target face agrees with the canonical target zero lift. -/
theorem quillenStageGridZeroComparisonLiftTarget_q :
    (quillenStageGridZeroComparisonLiftTarget F).q =
      (quillenStageGridTargetZeroLift (D := D)).q := by
  rw [quillenStageGridZeroComparisonLiftTarget,
    reindexQuillenStageGridLift_obj_q,
    quillenStageGridZeroComparisonLift_q]
  apply ComposableArrows.ext₀
  rfl

namespace QuillenStageGridZeroComparisonEdge.Internal

@[no_expose]
noncomputable def quillenStageGridMappedZeroFiber :
    QuillenStageGridFiber (quillenStageGridMappedZeroLift F).q :=
  ⟨quillenStageGridMappedZeroLift F, rfl⟩

@[no_expose]
noncomputable def quillenStageGridZeroComparisonLiftSourceFiber :
    QuillenStageGridFiber (quillenStageGridMappedZeroLift F).q :=
  ⟨quillenStageGridZeroComparisonLiftSource F,
    Discrete.ext (quillenStageGridZeroComparisonLiftSource_q F)⟩

@[no_expose]
noncomputable def quillenStageGridZeroComparisonLiftTargetFiber :
    QuillenStageGridFiber (quillenStageGridTargetZeroLift (D := D)).q :=
  ⟨quillenStageGridZeroComparisonLiftTarget F,
    Discrete.ext (quillenStageGridZeroComparisonLiftTarget_q F)⟩

@[no_expose]
noncomputable def quillenStageGridTargetZeroFiber :
    QuillenStageGridFiber (quillenStageGridTargetZeroLift (D := D)).q :=
  ⟨quillenStageGridTargetZeroLift (D := D), rfl⟩

@[no_expose]
noncomputable def quillenStageGridZeroComparisonLeftFiberHom :
    quillenStageGridMappedZeroLift F ⟶
      quillenStageGridZeroComparisonLiftSource F :=
  (QuillenStageGridFiberComparison.fiberHom
    (quillenStageGridMappedZeroFiber F) (quillenStageGridZeroComparisonLiftSourceFiber F)).1

@[no_expose]
noncomputable def quillenStageGridZeroComparisonRightFiberHom :
    quillenStageGridZeroComparisonLiftTarget F ⟶
      quillenStageGridTargetZeroLift (D := D) :=
  (QuillenStageGridFiberComparison.fiberHom
    (quillenStageGridZeroComparisonLiftTargetFiber F) (quillenStageGridTargetZeroFiber (D := D))).1

theorem reindexQuillenStageGrid_sigmaZero_delta_obj
    (X : QuillenStageGridLift D ⦋0⦌) (i : Fin 2) :
    ((reindexQuillenStageGridLift (C := D)
        (SimplexCategory.σ (0 : Fin 1)) ⋙
      reindexQuillenStageGridLift (C := D)
        (SimplexCategory.δ i)).obj X) = X := by
  fin_cases i
  · change ((reindexQuillenStageGridLift (C := D)
        (SimplexCategory.σ (0 : Fin 1)) ⋙
      reindexQuillenStageGridLift (C := D)
        (SimplexCategory.δ (0 : Fin 2))).obj X) = X
    rw [← reindexQuillenStageGridLift_comp]
    have hδσ : SimplexCategory.δ (0 : Fin 2) ≫
        SimplexCategory.σ (0 : Fin 1) =
        𝟙 (⦋0⦌ : SimplexCategory) := by
      simpa using SimplexCategory.δ_comp_σ_self
        (n := 0) (i := (0 : Fin 1))
    rw [hδσ, reindexQuillenStageGridLift_id]
    rfl
  · change ((reindexQuillenStageGridLift (C := D)
        (SimplexCategory.σ (0 : Fin 1)) ⋙
      reindexQuillenStageGridLift (C := D)
        (SimplexCategory.δ (1 : Fin 2))).obj X) = X
    rw [← reindexQuillenStageGridLift_comp]
    have hδσ : SimplexCategory.δ (1 : Fin 2) ≫
        SimplexCategory.σ (0 : Fin 1) =
        𝟙 (⦋0⦌ : SimplexCategory) := by
      simpa using SimplexCategory.δ_comp_σ_succ
        (n := 0) (i := (0 : Fin 1))
    rw [hδσ, reindexQuillenStageGridLift_id]
    rfl

end QuillenStageGridZeroComparisonEdge.Internal

/-- Underlying diagonal simplex induced by a morphism between degree-zero
Stage-grid lifts. -/
noncomputable def quillenStageGridDiagonalDegreeZeroMapSimplex
    {S T : QuillenStageGridLift D ⦋0⦌} (f : S ⟶ T) :
    (quillenStageGridDiagonal D).obj (op ⦋1⦌) :=
  ComposableArrows.mk₁
    ((reindexQuillenStageGridLift (C := D)
      (SimplexCategory.σ (0 : Fin 1))).map f)

/-- Diagonal edge induced by a morphism between degree-zero Stage-grid
lifts. -/
noncomputable def quillenStageGridDiagonalDegreeZeroMapEdge
    {S T : QuillenStageGridLift D ⦋0⦌} (f : S ⟶ T) :
    (quillenStageGridDiagonal D).Edge
      (ComposableArrows.mk₀ S) (ComposableArrows.mk₀ T) := by
  let s := quillenStageGridDiagonalDegreeZeroMapSimplex f
  refine SSet.Edge.ofEq (SSet.Edge.mk' s) ?_ ?_
  · have hInner :
        ((CategoryTheory.nerve (QuillenStageGridLift D ⦋1⦌)).map
          (SimplexCategory.δ 1).op) s =
          ComposableArrows.mk₀
            ((reindexQuillenStageGridLift (C := D)
              (SimplexCategory.σ (0 : Fin 1))).obj S) := by
      apply ComposableArrows.ext₀
      rfl
    have hOuter :
        (CategoryTheory.nerveMap
          (reindexQuillenStageGridLift (C := D)
            (SimplexCategory.δ 1))).app (op ⦋0⦌)
          (ComposableArrows.mk₀
            ((reindexQuillenStageGridLift (C := D)
              (SimplexCategory.σ (0 : Fin 1))).obj S)) =
          ComposableArrows.mk₀ S := by
      rw [CategoryTheory.nerveMap_app_mk₀]
      exact congrArg ComposableArrows.mk₀
        (reindexQuillenStageGrid_sigmaZero_delta_obj S 1)
    have hMap : (quillenStageGridDiagonal D).map
        (SimplexCategory.δ (1 : Fin 2)).op s =
      (CategoryTheory.nerveMap
        (reindexQuillenStageGridLift (C := D)
          (SimplexCategory.δ 1))).app (op ⦋0⦌)
        (((CategoryTheory.nerve (QuillenStageGridLift D ⦋1⦌)).map
          (SimplexCategory.δ 1).op) s) := rfl
    change (quillenStageGridDiagonal D).map
      (SimplexCategory.δ (1 : Fin 2)).op s = _
    rw [hMap, hInner, hOuter]
  · have hInner :
        ((CategoryTheory.nerve (QuillenStageGridLift D ⦋1⦌)).map
          (SimplexCategory.δ 0).op) s =
          ComposableArrows.mk₀
            ((reindexQuillenStageGridLift (C := D)
              (SimplexCategory.σ (0 : Fin 1))).obj T) := by
      apply ComposableArrows.ext₀
      rfl
    have hOuter :
        (CategoryTheory.nerveMap
          (reindexQuillenStageGridLift (C := D)
            (SimplexCategory.δ 0))).app (op ⦋0⦌)
          (ComposableArrows.mk₀
            ((reindexQuillenStageGridLift (C := D)
              (SimplexCategory.σ (0 : Fin 1))).obj T)) =
          ComposableArrows.mk₀ T := by
      rw [CategoryTheory.nerveMap_app_mk₀]
      exact congrArg ComposableArrows.mk₀
        (reindexQuillenStageGrid_sigmaZero_delta_obj T 0)
    have hMap : (quillenStageGridDiagonal D).map
        (SimplexCategory.δ (0 : Fin 2)).op s =
      (CategoryTheory.nerveMap
        (reindexQuillenStageGridLift (C := D)
          (SimplexCategory.δ 0))).app (op ⦋0⦌)
        (((CategoryTheory.nerve (QuillenStageGridLift D ⦋1⦌)).map
          (SimplexCategory.δ 0).op) s) := rfl
    change (quillenStageGridDiagonal D).map
      (SimplexCategory.δ (0 : Fin 2)).op s = _
    rw [hMap, hInner, hOuter]

/-- The underlying simplex of a degree-zero map edge. -/
@[simp]
theorem quillenStageGridDiagonalDegreeZeroMapEdge_edge
    {S T : QuillenStageGridLift D ⦋0⦌} (f : S ⟶ T) :
    (quillenStageGridDiagonalDegreeZeroMapEdge f).edge =
      quillenStageGridDiagonalDegreeZeroMapSimplex f :=
  rfl

/-- Source formula for the degree-zero diagonal map edge. -/
@[simp]
theorem quillenStageGridDiagonalDegreeZeroMapEdge_src
    {S T : QuillenStageGridLift D ⦋0⦌} (f : S ⟶ T) :
    (quillenStageGridDiagonal D).δ 1
        (quillenStageGridDiagonalDegreeZeroMapEdge f).edge =
      ComposableArrows.mk₀ S :=
  SSet.Edge.src_eq _

/-- Target formula for the degree-zero diagonal map edge. -/
@[simp]
theorem quillenStageGridDiagonalDegreeZeroMapEdge_tgt
    {S T : QuillenStageGridLift D ⦋0⦌} (f : S ⟶ T) :
    (quillenStageGridDiagonal D).δ 0
        (quillenStageGridDiagonalDegreeZeroMapEdge f).edge =
      ComposableArrows.mk₀ T :=
  SSet.Edge.tgt_eq _

/-- Central diagonal simplex given by the identity of the selected lift. -/
noncomputable def quillenStageGridDiagonalZeroComparisonCentralSimplex :
    (quillenStageGridDiagonal D).obj (op ⦋1⦌) :=
  ComposableArrows.mk₁ (𝟙 (quillenStageGridZeroComparisonLift F))

/-- The central diagonal edge, from the source face to the target face of the
selected zero-comparison lift. -/
noncomputable def quillenStageGridDiagonalZeroComparisonCentralEdge :
    (quillenStageGridDiagonal D).Edge
      (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftSource F))
      (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftTarget F)) := by
  let s := quillenStageGridDiagonalZeroComparisonCentralSimplex F
  refine SSet.Edge.ofEq (SSet.Edge.mk' s) ?_ ?_
  · have hInner :
        ((CategoryTheory.nerve (QuillenStageGridLift D ⦋1⦌)).map
          (SimplexCategory.δ 1).op) s =
          ComposableArrows.mk₀ (quillenStageGridZeroComparisonLift F) := by
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
          ComposableArrows.mk₀ (quillenStageGridZeroComparisonLift F) := by
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
noncomputable def quillenStageGridDiagonalZeroComparisonLeftEdge :
    (quillenStageGridDiagonal D).Edge
      (ComposableArrows.mk₀ (quillenStageGridMappedZeroLift F))
      (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftSource F)) :=
  quillenStageGridDiagonalDegreeZeroMapEdge (quillenStageGridZeroComparisonLeftFiberHom F)

/-- Right connector from the selected lift's target face to the canonical
target zero lift, built from the direct strict-fiber comparison. -/
noncomputable def quillenStageGridDiagonalZeroComparisonRightEdge :
    (quillenStageGridDiagonal D).Edge
      (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftTarget F))
      (ComposableArrows.mk₀ (quillenStageGridTargetZeroLift (D := D))) :=
  quillenStageGridDiagonalDegreeZeroMapEdge (quillenStageGridZeroComparisonRightFiberHom F)

/-- Raw realized concatenation of the left, central, and right Stage-grid
edges.  Its endpoints are realized lift vertices, before any basepoint cast. -/
noncomputable def quillenStageGridDiagonalZeroComparisonRawPath :
    Path
      (SSet.realizedVertex (ComposableArrows.mk₀ (quillenStageGridMappedZeroLift F)))
      (SSet.realizedVertex (X := quillenStageGridDiagonal D)
        (ComposableArrows.mk₀
        (quillenStageGridTargetZeroLift (D := D)))) :=
  (TopCat.pathEquiv
    (SSet.realizedEdgePath
      (quillenStageGridDiagonalZeroComparisonLeftEdge F))).trans
    ((TopCat.pathEquiv
      (SSet.realizedEdgePath
        (quillenStageGridDiagonalZeroComparisonCentralEdge F))).trans
      (TopCat.pathEquiv
        (SSet.realizedEdgePath
          (quillenStageGridDiagonalZeroComparisonRightEdge F))))
set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero vertices project to their retained Quillen vertices. -/
theorem quillenStageGridToNQ_mk₀ (X : QuillenStageGridLift D ⦋0⦌) :
    (quillenStageGridToNQ (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ X) = X.q := by
  change (quillenQSimplexDiscreteDiagonalIso (C := D)).hom.app (op ⦋0⦌)
      ((quillenStageGridQProjectionDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ X)) = _
  rw [quillenStageGridQProjectionDiagonal_app]
  simp only [unop_op]
  change (SSet.nerveDiscreteObjEquiv (QuillenQSimplex D ⦋0⦌) (op ⦋0⦌))
      ((CategoryTheory.nerveMap
        (quillenStageGridQProjection D ⦋0⦌)).app (op ⦋0⦌)
          (ComposableArrows.mk₀ X)) = _
  rw [CategoryTheory.nerveMap_app_mk₀]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The retained simplex of the canonical zero lift is the Q zero vertex. -/
theorem quillenStageGridZeroLift_q (E : Type u) [Category.{v} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    (quillenStageGridZeroLift E).q = NQ.zeroVertex E := by
  have h := quillenStageGridToNQ_zeroVertex (C := E)
  change (quillenStageGridToNQ (C := E)).app (op ⦋0⦌)
      (ComposableArrows.mk₀ (quillenStageGridZeroLift E)) = NQ.zeroVertex E at h
  rw [quillenStageGridToNQ_mk₀] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The mapped zero lift projects to the mapped Q zero vertex. -/
theorem quillenStageGridMappedZeroLift_toNQ :
    (quillenStageGridToNQ (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (quillenStageGridMappedZeroLift F)) =
      (NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C) := by
  rw [quillenStageGridToNQ_mk₀]
  rw [quillenStageGridMappedZeroLift, quillenStageGridLiftMap_obj_q, quillenStageGridZeroLift_q]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The source face of the selected lift projects to the mapped Q zero
vertex. -/
theorem quillenStageGridZeroComparisonLiftSource_toNQ :
    (quillenStageGridToNQ (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftSource F)) =
      (NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C) := by
  rw [quillenStageGridToNQ_mk₀]
  rw [quillenStageGridZeroComparisonLiftSource_q]
  rw [← quillenStageGridToNQ_mk₀]
  exact quillenStageGridMappedZeroLift_toNQ F

set_option backward.isDefEq.respectTransparency false in
/-- The target zero lift projects to the target Q zero vertex. -/
theorem quillenStageGridTargetZeroLift_toNQ :
    (quillenStageGridToNQ (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (quillenStageGridTargetZeroLift (D := D))) =
      NQ.zeroVertex D := by
  rw [quillenStageGridToNQ_mk₀]
  exact quillenStageGridZeroLift_q D

set_option backward.isDefEq.respectTransparency false in
/-- The target face of the selected lift projects to the target Q zero
vertex. -/
theorem quillenStageGridZeroComparisonLiftTarget_toNQ :
    (quillenStageGridToNQ (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftTarget F)) =
      NQ.zeroVertex D := by
  rw [quillenStageGridToNQ_mk₀]
  rw [quillenStageGridZeroComparisonLiftTarget_q]
  rw [← quillenStageGridToNQ_mk₀]
  exact quillenStageGridTargetZeroLift_toNQ (D := D)

set_option backward.isDefEq.respectTransparency false in
/-- The underlying Q projection of the left connector is degenerate. -/
theorem quillenStageGridDiagonalZeroComparisonLeftEdge_toNQ_edge :
    ((quillenStageGridDiagonalZeroComparisonLeftEdge F).map (quillenStageGridToNQ (C := D))).edge =
      (SSet.Edge.id
        ((quillenStageGridToNQ (C := D)).app (op ⦋0⦌)
          (ComposableArrows.mk₀ (quillenStageGridMappedZeroLift F)))).edge := by
  rw [SSet.Edge.map_edge]
  change (quillenStageGridToNQ (C := D)).app (op ⦋1⦌)
      (quillenStageGridDiagonalDegreeZeroMapSimplex
        (quillenStageGridZeroComparisonLeftFiberHom F)) = _
  change (quillenQSimplexDiscreteDiagonalIso (C := D)).hom.app (op ⦋1⦌)
      ((quillenStageGridQProjectionDiagonal (C := D)).app (op ⦋1⦌)
        (quillenStageGridDiagonalDegreeZeroMapSimplex
          (quillenStageGridZeroComparisonLeftFiberHom F))) = _
  rw [quillenStageGridQProjectionDiagonal_app]
  simp only [unop_op]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The underlying Q projection of the central connector is the canonical
zero-comparison simplex. -/
theorem quillenStageGridDiagonalZeroComparisonCentralEdge_toNQ_edge :
    ((quillenStageGridDiagonalZeroComparisonCentralEdge F).map
      (quillenStageGridToNQ (C := D))).edge =
      (NQ.zeroComparisonEdge F).edge := by
  rw [SSet.Edge.map_edge]
  change (quillenStageGridToNQ (C := D)).app (op ⦋1⦌)
      (quillenStageGridDiagonalZeroComparisonCentralSimplex F) = (NQ.zeroComparisonEdge F).edge
  change (quillenQSimplexDiscreteDiagonalIso (C := D)).hom.app (op ⦋1⦌)
      ((quillenStageGridQProjectionDiagonal (C := D)).app (op ⦋1⦌)
        (quillenStageGridDiagonalZeroComparisonCentralSimplex F)) = _
  rw [quillenStageGridQProjectionDiagonal_app]
  simp only [unop_op]
  change (quillenStageGridZeroComparisonLift F).q = (NQ.zeroComparisonEdge F).edge
  exact quillenStageGridZeroComparisonLift_q F

set_option backward.isDefEq.respectTransparency false in
/-- The underlying Q projection of the right connector is degenerate. -/
theorem quillenStageGridDiagonalZeroComparisonRightEdge_toNQ_edge :
    ((quillenStageGridDiagonalZeroComparisonRightEdge F).map (quillenStageGridToNQ (C := D))).edge =
      (SSet.Edge.id
        ((quillenStageGridToNQ (C := D)).app (op ⦋0⦌)
          (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftTarget F)))).edge := by
  rw [SSet.Edge.map_edge]
  change (quillenStageGridToNQ (C := D)).app (op ⦋1⦌)
      (quillenStageGridDiagonalDegreeZeroMapSimplex
        (quillenStageGridZeroComparisonRightFiberHom F)) = _
  change (quillenQSimplexDiscreteDiagonalIso (C := D)).hom.app (op ⦋1⦌)
      ((quillenStageGridQProjectionDiagonal (C := D)).app (op ⦋1⦌)
        (quillenStageGridDiagonalDegreeZeroMapSimplex
          (quillenStageGridZeroComparisonRightFiberHom F))) = _
  rw [quillenStageGridQProjectionDiagonal_app]
  simp only [unop_op]
  rfl

/-- Left Q projection with endpoints transported to the mapped zero vertex. -/
noncomputable def quillenStageGridZeroComparisonLeftQEdge :
    (NQ D).Edge
      ((NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C))
      ((NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C)) :=
  ((quillenStageGridDiagonalZeroComparisonLeftEdge F).map (quillenStageGridToNQ (C := D))).ofEq
    (quillenStageGridMappedZeroLift_toNQ F) (quillenStageGridZeroComparisonLiftSource_toNQ F)

/-- Central Q projection with canonical zero-comparison endpoints. -/
noncomputable def quillenStageGridZeroComparisonCentralQEdge :
    (NQ D).Edge
      ((NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C))
      (NQ.zeroVertex D) :=
  ((quillenStageGridDiagonalZeroComparisonCentralEdge F).map (quillenStageGridToNQ (C := D))).ofEq
    (quillenStageGridZeroComparisonLiftSource_toNQ F)
    (quillenStageGridZeroComparisonLiftTarget_toNQ F)

/-- Right Q projection with endpoints transported to the target zero vertex. -/
noncomputable def quillenStageGridZeroComparisonRightQEdge :
    (NQ D).Edge (NQ.zeroVertex D) (NQ.zeroVertex D) :=
  ((quillenStageGridDiagonalZeroComparisonRightEdge F).map (quillenStageGridToNQ (C := D))).ofEq
    (quillenStageGridZeroComparisonLiftTarget_toNQ F) (quillenStageGridTargetZeroLift_toNQ (D := D))

set_option backward.isDefEq.respectTransparency false in
/-- The left Q projection is the identity edge. -/
theorem quillenStageGridZeroComparisonLeftQEdge_eq_id :
    quillenStageGridZeroComparisonLeftQEdge F = SSet.Edge.id
      ((NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C)) := by
  apply SSet.Edge.ext
  change ((quillenStageGridDiagonalZeroComparisonLeftEdge F).map
    (quillenStageGridToNQ (C := D))).edge = _
  rw [← quillenStageGridMappedZeroLift_toNQ F]
  exact quillenStageGridDiagonalZeroComparisonLeftEdge_toNQ_edge F

set_option backward.isDefEq.respectTransparency false in
/-- The central Q projection is the canonical zero-comparison edge. -/
theorem quillenStageGridZeroComparisonCentralQEdge_eq_zeroComparison :
    quillenStageGridZeroComparisonCentralQEdge F = NQ.zeroComparisonEdge F := by
  apply SSet.Edge.ext
  exact quillenStageGridDiagonalZeroComparisonCentralEdge_toNQ_edge F

set_option backward.isDefEq.respectTransparency false in
/-- The right Q projection is the identity edge. -/
theorem quillenStageGridZeroComparisonRightQEdge_eq_id :
    quillenStageGridZeroComparisonRightQEdge F = SSet.Edge.id (NQ.zeroVertex D) := by
  apply SSet.Edge.ext
  change ((quillenStageGridDiagonalZeroComparisonRightEdge F).map
    (quillenStageGridToNQ (C := D))).edge = _
  rw [← quillenStageGridZeroComparisonLiftTarget_toNQ F]
  exact quillenStageGridDiagonalZeroComparisonRightEdge_toNQ_edge F

/-- Raw concatenation of the three realized Q projections. -/
noncomputable def quillenStageGridZeroComparisonQProjectionPath :
    Path
      (SSet.realizedVertex
        ((NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C)))
      (SSet.realizedVertex (NQ.zeroVertex D)) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath (quillenStageGridZeroComparisonLeftQEdge F))).trans
    ((TopCat.pathEquiv (SSet.realizedEdgePath (quillenStageGridZeroComparisonCentralQEdge F))).trans
      (TopCat.pathEquiv (SSet.realizedEdgePath (quillenStageGridZeroComparisonRightQEdge F))))

/-- The raw Q projection path is homotopic to the realized canonical
zero-comparison edge. -/
theorem quillenStageGridZeroComparisonQProjectionPath_homotopic_zeroComparison :
    (quillenStageGridZeroComparisonQProjectionPath F).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (NQ.zeroComparisonEdge F))) := by
  rw [quillenStageGridZeroComparisonQProjectionPath,
    quillenStageGridZeroComparisonLeftQEdge_eq_id,
    quillenStageGridZeroComparisonCentralQEdge_eq_zeroComparison,
    quillenStageGridZeroComparisonRightQEdge_eq_id]
  let q0 := (NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C)
  let q1 := NQ.zeroVertex D
  let i0 := TopCat.pathEquiv
    (SSet.realizedEdgePath (SSet.Edge.id q0))
  let p := TopCat.pathEquiv
    (SSet.realizedEdgePath (NQ.zeroComparisonEdge F))
  let i1 := TopCat.pathEquiv
    (SSet.realizedEdgePath (SSet.Edge.id q1))
  have hi0 : i0.Homotopic (Path.refl (SSet.realizedVertex q0)) :=
    SSet.realizedEdgePath_id_homotopic q0
  have hi1 : i1.Homotopic (Path.refl (SSet.realizedVertex q1)) :=
    SSet.realizedEdgePath_id_homotopic q1
  have hRight : (p.trans i1).Homotopic p :=
    ((Path.Homotopic.refl p).hcomp hi1).trans
      (Path.Homotopic.trans_refl p)
  exact (hi0.hcomp hRight).trans (Path.Homotopic.refl_trans p)
set_option backward.isDefEq.respectTransparency false in
/-- A degree-zero map edge has zero Stage-one off-diagonal component after
projection to the Stage diagonal. -/
theorem quillenStageGridDiagonalDegreeZeroMapEdge_toStage_offdiag_isZero
    {S T : QuillenStageGridLift D ⦋0⦌} (f : S ⟶ T) :
    IsZero ((stageOneEval D).obj
      (ComposableArrows.left
        ((quillenStageGridDiagonalDegreeZeroMapEdge f).map
          (quillenStageGridToStageWeakDiagonal (C := D))).edge).obj) := by
  change IsZero (S.grid.obj.obj.obj (diag (1 : Fin 2)))
  exact S.grid.obj.property.diag_isZero 1

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero grid vertices project to the reindexed Stage-zero vertex. -/
theorem quillenStageGridToStage_mk₀ (X : QuillenStageGridLift D ⦋0⦌) :
    (quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀
        ((reindexStageWeak D (SimplexCategory.δ 0)).obj X.grid) := by
  change (outerEdgewiseStageDiagonalComparison (C := D)).app (op ⦋0⦌)
      ((quillenStageGridStageProjectionDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ X)) = _
  rw [quillenStageGridStageProjectionDiagonal_app_mk₀,
    outerEdgewiseStageDiagonalComparison_app,
    SimplexCategory.edgewiseRightInclusion_app_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The target zero lift projects to the Stage zero vertex. -/
theorem quillenStageGridTargetZeroLift_toStage :
    (quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (quillenStageGridTargetZeroLift (D := D))) =
      stageWeakDiagonalZeroVertex D := by
  rw [quillenStageGridToStage_mk₀]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The mapped zero lift projects to the source of the canonical level-zero
Stage edge. -/
theorem quillenStageGridMappedZeroLift_toStage :
    (quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (quillenStageGridMappedZeroLift F)) =
      levelZeroEdgeMappedVertex C D F := by
  rw [quillenStageGridToStage_mk₀]
  rfl

/-- Left Stage projection with its source transported to the canonical
level-zero mapped vertex. -/
noncomputable def quillenStageGridZeroComparisonLeftStageEdge :
    (stageWeakDiagonal D).Edge (levelZeroEdgeMappedVertex C D F)
      ((quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftSource F))) :=
  ((quillenStageGridDiagonalZeroComparisonLeftEdge F).map
    (quillenStageGridToStageWeakDiagonal (C := D))).ofEq
      (quillenStageGridMappedZeroLift_toStage F) rfl

/-- Central Stage projection of the selected zero-comparison lift. -/
noncomputable def quillenStageGridZeroComparisonCentralStageEdge :
    (stageWeakDiagonal D).Edge
      ((quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftSource F)))
      ((quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftTarget F))) :=
  (quillenStageGridDiagonalZeroComparisonCentralEdge F).map
    (quillenStageGridToStageWeakDiagonal (C := D))

/-- Right Stage projection with its target transported to the Stage zero
vertex. -/
noncomputable def quillenStageGridZeroComparisonRightStageEdge :
    (stageWeakDiagonal D).Edge
      ((quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftTarget F)))
      (stageWeakDiagonalZeroVertex D) :=
  ((quillenStageGridDiagonalZeroComparisonRightEdge F).map
    (quillenStageGridToStageWeakDiagonal (C := D))).ofEq
      rfl (quillenStageGridTargetZeroLift_toStage (D := D))

/-- Raw concatenation of the three realized Stage projections. -/
noncomputable def quillenStageGridZeroComparisonStageProjectionPath :
    Path
      (SSet.realizedVertex (levelZeroEdgeMappedVertex C D F))
      (SSet.realizedVertex (stageWeakDiagonalZeroVertex D)) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath (quillenStageGridZeroComparisonLeftStageEdge F))).trans
    ((TopCat.pathEquiv
      (SSet.realizedEdgePath (quillenStageGridZeroComparisonCentralStageEdge F))).trans
      (TopCat.pathEquiv (SSet.realizedEdgePath (quillenStageGridZeroComparisonRightStageEdge F))))

set_option backward.isDefEq.respectTransparency false in
/-- The central Stage projection has zero off-diagonal component.  The proof
uses the selected Q-lift agreement, the normalized shell, and its exact
quotient sequence; no zero condition is assumed. -/
theorem quillenStageGridDiagonalZeroComparisonCentralEdge_toStage_offdiag_isZero :
    IsZero ((stageOneEval D).obj
      (ComposableArrows.left
        ((quillenStageGridDiagonalZeroComparisonCentralEdge F).map
          (quillenStageGridToStageWeakDiagonal (C := D))).edge).obj) := by
  change IsZero ((quillenStageGridZeroComparisonLift F).grid.obj.obj.obj
    (interval (2 : Fin 4) 3 (by decide)))
  let X := quillenStageGridZeroComparisonLift F
  let A := X.grid.obj
  have hqObj : X.q.obj (1 : Fin 2) = (⟨(0 : D)⟩ : QuillenQ D) := by
    dsimp only [X]
    rw [quillenStageGridZeroComparisonLift_q]
    rfl
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

set_option backward.isDefEq.respectTransparency false in
/-- The left Stage projection has zero off-diagonal component. -/
theorem quillenStageGridZeroComparisonLeftStageEdge_offdiag_isZero :
    IsZero ((stageOneEval D).obj
      (ComposableArrows.left (quillenStageGridZeroComparisonLeftStageEdge F).edge).obj) := by
  exact quillenStageGridDiagonalDegreeZeroMapEdge_toStage_offdiag_isZero
    (quillenStageGridZeroComparisonLeftFiberHom F)

set_option backward.isDefEq.respectTransparency false in
/-- The central Stage projection has zero off-diagonal component. -/
theorem quillenStageGridZeroComparisonCentralStageEdge_offdiag_isZero :
    IsZero ((stageOneEval D).obj
      (ComposableArrows.left (quillenStageGridZeroComparisonCentralStageEdge F).edge).obj) := by
  exact quillenStageGridDiagonalZeroComparisonCentralEdge_toStage_offdiag_isZero F

set_option backward.isDefEq.respectTransparency false in
/-- The right Stage projection has zero off-diagonal component. -/
theorem quillenStageGridZeroComparisonRightStageEdge_offdiag_isZero :
    IsZero ((stageOneEval D).obj
      (ComposableArrows.left (quillenStageGridZeroComparisonRightStageEdge F).edge).obj) := by
  exact quillenStageGridDiagonalDegreeZeroMapEdge_toStage_offdiag_isZero
    (quillenStageGridZeroComparisonRightFiberHom F)

set_option backward.isDefEq.respectTransparency false in
/-- The raw Stage projection path telescopes, in the fundamental groupoid,
to the realized canonical level-zero Stage edge. -/
theorem quillenStageGridZeroComparisonStageProjectionPath_homotopic_levelZero :
    (quillenStageGridZeroComparisonStageProjectionPath F).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalLevelZeroEdge C D F))) := by
  let eL := quillenStageGridZeroComparisonLeftStageEdge F
  let eC := quillenStageGridZeroComparisonCentralStageEdge F
  let eR := quillenStageGridZeroComparisonRightStageEdge F
  let e0 := stageWeakDiagonalLevelZeroEdge C D F
  let pL := TopCat.pathEquiv (SSet.realizedEdgePath eL)
  let pC := TopCat.pathEquiv (SSet.realizedEdgePath eC)
  let pR := TopCat.pathEquiv (SSet.realizedEdgePath eR)
  let p0 := TopCat.pathEquiv (SSet.realizedEdgePath e0)
  let xS := (quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
    (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftSource F))
  let xT := (quillenStageGridToStageWeakDiagonal (C := D)).app (op ⦋0⦌)
    (ComposableArrows.mk₀ (quillenStageGridZeroComparisonLiftTarget F))
  let cM := TopCat.pathEquiv (SSet.realizedEdgePath
    (stageWeakDiagonalZeroToVertexEdge D
      (levelZeroEdgeMappedVertex C D F)))
  let cS := TopCat.pathEquiv (SSet.realizedEdgePath
    (stageWeakDiagonalZeroToVertexEdge D xS))
  let cT := TopCat.pathEquiv (SSet.realizedEdgePath
    (stageWeakDiagonalZeroToVertexEdge D xT))
  let cZ := TopCat.pathEquiv (SSet.realizedEdgePath
    (stageWeakDiagonalZeroToVertexEdge D
      (stageWeakDiagonalZeroVertex D)))
  have hL : (pL.trans cS.symm).Homotopic cM.symm := by
    exact stageWeakDiagonalEdge_comp_zeroConnectorSymm_homotopic_of_isZero
      D eL (quillenStageGridZeroComparisonLeftStageEdge_offdiag_isZero F)
  have hC : (pC.trans cT.symm).Homotopic cS.symm := by
    exact stageWeakDiagonalEdge_comp_zeroConnectorSymm_homotopic_of_isZero
      D eC (quillenStageGridZeroComparisonCentralStageEdge_offdiag_isZero F)
  have hR : (pR.trans cZ.symm).Homotopic cT.symm := by
    exact stageWeakDiagonalEdge_comp_zeroConnectorSymm_homotopic_of_isZero
      D eR (quillenStageGridZeroComparisonRightStageEdge_offdiag_isZero F)
  have hzero0 : IsZero ((stageOneEval D).obj
      (ComposableArrows.left e0.edge).obj) := by
    dsimp only [e0]
    rw [stageWeakDiagonalLevelZeroEdge_edge]
    change IsZero (F.obj (0 : C))
    exact F.map_isZero (isZero_zero C)
  have h0 : (p0.trans cZ.symm).Homotopic cM.symm := by
    exact stageWeakDiagonalEdge_comp_zeroConnectorSymm_homotopic_of_isZero
      D e0 hzero0
  have hLq := Path.Homotopic.Quotient.eq.mpr hL
  have hCq := Path.Homotopic.Quotient.eq.mpr hC
  have hRq := Path.Homotopic.Quotient.eq.mpr hR
  have h0q := Path.Homotopic.Quotient.eq.mpr h0
  simp only [Path.Homotopic.Quotient.mk_trans] at hLq hCq hRq h0q
  let m := SSet.realizedVertex (levelZeroEdgeMappedVertex C D F)
  let s := SSet.realizedVertex xS
  let t := SSet.realizedVertex xT
  let z := SSet.realizedVertex (stageWeakDiagonalZeroVertex D)
  let qL : _root_.FundamentalGroupoid.mk m ⟶
      _root_.FundamentalGroupoid.mk s :=
    Path.Homotopic.Quotient.mk pL
  let qC : _root_.FundamentalGroupoid.mk s ⟶
      _root_.FundamentalGroupoid.mk t :=
    Path.Homotopic.Quotient.mk pC
  let qR : _root_.FundamentalGroupoid.mk t ⟶
      _root_.FundamentalGroupoid.mk z :=
    Path.Homotopic.Quotient.mk pR
  let q0 : _root_.FundamentalGroupoid.mk m ⟶
      _root_.FundamentalGroupoid.mk z :=
    Path.Homotopic.Quotient.mk p0
  let qM : _root_.FundamentalGroupoid.mk m ⟶
      _root_.FundamentalGroupoid.mk z :=
    Path.Homotopic.Quotient.mk cM.symm
  let qS : _root_.FundamentalGroupoid.mk s ⟶
      _root_.FundamentalGroupoid.mk z :=
    Path.Homotopic.Quotient.mk cS.symm
  let qT : _root_.FundamentalGroupoid.mk t ⟶
      _root_.FundamentalGroupoid.mk z :=
    Path.Homotopic.Quotient.mk cT.symm
  let qZ : _root_.FundamentalGroupoid.mk z ⟶
      _root_.FundamentalGroupoid.mk z :=
    Path.Homotopic.Quotient.mk cZ.symm
  change qL ≫ qS = qM at hLq
  change qC ≫ qT = qS at hCq
  change qR ≫ qZ = qT at hRq
  change q0 ≫ qZ = qM at h0q
  have hcat :
      (qL ≫ (qC ≫ qR)) ≫ qZ = q0 ≫ qZ := by
    calc
      _ = qL ≫ (qC ≫ (qR ≫ qZ)) := by
            simp only [Category.assoc]
      _ = qL ≫ (qC ≫ qT) := by rw [hRq]
      _ = qL ≫ qS := by rw [hCq]
      _ = qM := hLq
      _ = q0 ≫ qZ := h0q.symm
  have hbare :
      qL ≫ (qC ≫ qR) = q0 :=
    (cancel_mono qZ).mp hcat
  change (pL.trans (pC.trans pR)).Homotopic p0
  apply Path.Homotopic.Quotient.eq.mp
  simpa only [qL, qC, qR, q0,
    Path.Homotopic.Quotient.mk_trans,
    _root_.FundamentalGroupoid.comp_eq] using hbare


end AlgebraicKTheory

end
