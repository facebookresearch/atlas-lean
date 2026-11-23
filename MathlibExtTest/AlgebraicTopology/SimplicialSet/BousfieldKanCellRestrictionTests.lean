/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanCellRestriction

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Topology
open scoped Simplicial

universe u

namespace SSet

variable {J : Type u} [Category.{0} J] (D : J ⥤ SSet.{u})

-- Epi normalization preserves the original first coefficient structurally.
example {m n : ℕ} (c : ComposableArrows J n) (θ : ⦋m⦌ ⟶ ⦋n⦌) [Epi θ] :
    IsIso (D.map (bkChainFirstArrow c θ)) := by
  let := bkChainFirstArrow_isIso_of_epi c θ
  infer_instance

-- The boundary map is accessible without opening its definition body.
example {n : ℕ} (c : ComposableArrows J n)
    (q : toTop.obj (D.obj c.left) × Convexity.StdSimplex ℝ (Fin (n + 1))) :
    bkRealizedChainCellToStage D c q =
      toTop.map (bkChainCellToStage D c) ((bkChainCellProductIso D c).inv q) := by
  rw [bkRealizedChainCellToStage_eq]
  rfl

-- The first coefficient follows the actual forward arrow for every simplex map.
example {m n : ℕ} (c : ComposableArrows J n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (D.obj c.left ◁ (SSet.stdSimplex : SimplexCategory ⥤ SSet.{u}).map θ) ≫
      bkChainCellMap D c =
    (D.map (bkChainFirstArrow c θ) ▷ (Δ[m] : SSet.{u})) ≫
      bkChainCellMap D ((nerve J).map θ.op c) :=
  bkChainCellMap_reindex D c θ

-- A whole nerve cell is not required to be mono, and its faces may degenerate.
example (n : ℕ) (c : (nerve J).nonDegenerate (n + 1)) :
    (bkSkeletalFiltration D n).preimage (bkChainCellMap D c.1) =
      (⊤ : (D.obj c.1.left).Subcomplex).prod (boundary (n + 1)) :=
  bkChainCellMap_preimage_stage D c

example (n : ℕ) :
    IsPushout (bkNondegenerateCellAttachment D n)
      (bkNondegenerateCellBoundaryInclusion D (n + 1))
      (bkSkeletalFiltrationMap D (Nat.le_succ n))
      (bkNondegenerateCellToStage D (n + 1)) :=
  bkSkeletalFiltrationSucc_nonDegenerate_isPushout D n

example (n : ℕ) :
    IsPushout (toTop.map (bkNondegenerateCellAttachment D n))
      (toTop.map (bkNondegenerateCellBoundaryInclusion D (n + 1)))
      (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n)))
      (toTop.map (bkNondegenerateCellToStage D (n + 1))) :=
  bkSkeletalFiltrationSucc_nonDegenerate_realized_isPushout D n

example (n : ℕ) : Mono (bkNondegenerateCellBoundaryInclusion D n) := inferInstance

-- Native product coordinates work with arbitrary coefficient universes.
example {n : ℕ} (c : ComposableArrows J n)
    (q : toTop.obj (D.obj c.left ⊗ (Δ[n] : SSet.{u}))) :
    (bkChainCellProductIso D c).hom q =
      (toTop.map (CartesianMonoidalCategory.fst (D.obj c.left) (Δ[n] : SSet.{u})) q,
        SimplexCategory.toTopHomeo.{u} ⦋n⦌
          (toTop.map (CartesianMonoidalCategory.snd (D.obj c.left) (Δ[n] : SSet.{u})) q)) :=
  bkChainCellProductIso_hom_apply D c q

example {m n : ℕ} (c : ComposableArrows J n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    TopCat.ofHom ((ContinuousMap.id (toTop.obj (D.obj c.left))).prodMap
        (stdSimplex.toTopMap θ).hom) ≫ bkRealizedChainCell D c =
      TopCat.ofHom ((toTop.map (D.map (bkChainFirstArrow c θ))).hom.prodMap
        (ContinuousMap.id (Convexity.StdSimplex ℝ (Fin (m + 1))))) ≫
          bkRealizedChainCell D ((nerve J).map θ.op c) :=
  bkRealizedChainCell_reindex D c θ

example (n : ℕ)
    (z : Σ c : (nerve J).nonDegenerate n,
      toTop.obj (D.obj c.1.left) × Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (bkNondegenerateCellsProductIso D n).inv z ∈
      Set.range (toTop.map (bkNondegenerateCellBoundaryInclusion D n)) ↔
        ∃ i, z.2.2.weights i = 0 :=
  bkNondegenerateCellsProductIso_inv_mem_boundary_iff D n z

-- The chart is the actual cell map into its stage, with its original base coordinate.
example (n : ℕ) (c : (nerve J).nonDegenerate (n + 1))
    (x : toTop.obj (D.obj c.1.left))
    (t : {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) :
    toTop.map (bkHocolimToNerve D)
      (toTop.map (bkSkeletalFiltration D (n + 1)).ι
        (((bkNondegenerateCellInteriorProductIso D n).hom ⟨c, x, t⟩).1)) =
      toTop.map (yonedaEquiv.symm c.1 : (Δ[n + 1] : SSet.{u}) ⟶ nerve J)
        ((SimplexCategory.toTopHomeo.{u} ⦋n + 1⦌).symm t.1) := by
  have hi := bkNondegenerateCellInteriorProductIso_hom_apply D n c x t
  have hc := ConcreteCategory.congr_hom (bkRealizedChainCellToStage_ι D c.1) (x, t.1)
  have ht := (congrArg (fun z => toTop.map (bkSkeletalFiltration D (n + 1)).ι z) hi).trans hc
  exact (congrArg (fun z => toTop.map (bkHocolimToNerve D) z) ht).trans
    (bkRealizedChainCell_projection_apply D c.1 x t.1)

end SSet
