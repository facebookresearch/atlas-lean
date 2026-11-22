/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectContraction
import MathlibExt.AlgebraicTopology.SimplicialSet.EquifibredDiagonalPullback
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPointFibre
import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoopsRealizedConull

/-!
# The original based fixed-object path diagonal

The actual extra-degeneracy section supplies its original identity-edge
basepoint. Its path projection is the same prescribed object in the original
diagonal. The whole fixed-object diagonal has a weak terminal map, so the
existing based contraction gives a full compact-open homotopy-fibre/loop
equivalence with its actual forward map and both actual inverse families.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The original inverse row isomorphism retains its complete shifted-simplex projection. -/
theorem rowIso_inv_fst (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    (rowIso W x n).inv ≫ (toDecalage W x).app (op (SimplexCategory.mk n)) =
      pullback.fst ((SimplicialObject.LeftDecalage.augmentation W.diagram).app
        (op (SimplexCategory.mk n))) (SSet.yonedaEquiv.symm x) := by
  apply (cancel_epi (rowIso W x n).hom).mp
  simp only [Iso.hom_inv_id_assoc, rowIso_fst]

set_option backward.isDefEq.respectTransparency false in
/-- The actual identity section displayed at its original point and zero-row carriers. -/
def sectionZero (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ (diagram W x).obj (op (SimplexCategory.mk 0)) :=
  pullback.lift (SSet.yonedaEquiv.symm x ≫ W.diagram.map (SimplexCategory.σ (0 : Fin 1)).op)
      (𝟙 (Δ[0] : SSet.{u})) (by
        rw [Category.id_comp, Category.assoc]
        change SSet.yonedaEquiv.symm x ≫ W.diagram.map (SimplexCategory.σ (0 : Fin 1)).op ≫
          W.diagram.map (SimplicialObject.LeftDecalage.firstVertex.app (SimplexCategory.mk 0)).op = _
        rw [← W.diagram.map_comp, ← op_comp]
        have he : SimplicialObject.LeftDecalage.firstVertex.app (SimplexCategory.mk 0) ≫
            SimplexCategory.σ (0 : Fin 1) = 𝟙 (SimplexCategory.mk 0) := by
          ext i
          fin_cases i
          rfl
        rw [he]
        have hi : (𝟙 (SimplexCategory.mk 0)).op = 𝟙 (op (SimplexCategory.mk 0)) := rfl
        rw [hi, W.diagram.map_id, Category.comp_id]
        exact rfl) ≫ (rowIso W x 0).inv

set_option backward.isDefEq.respectTransparency false in
/-- The literal identity section retains the actual original degeneracy edge. -/
theorem sectionZero_fst (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    sectionZero W x ≫ (toDecalage W x).app (op (SimplexCategory.mk 0)) =
      SSet.yonedaEquiv.symm x ≫ W.diagram.map (SimplexCategory.σ (0 : Fin 1)).op := by
  rw [sectionZero, Category.assoc, rowIso_inv_fst, pullback.lift_fst]

set_option backward.isDefEq.respectTransparency false in
/-- The same whole original extra-degeneracy section projects to the prescribed object. -/
theorem sectionZero_projection (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    sectionZero W x ≫ (projection W x).app (op (SimplexCategory.mk 0)) = SSet.yonedaEquiv.symm x := by
  have hs := sectionZero_fst W x
  change sectionZero W x ≫ ((toDecalage W x).app (op (SimplexCategory.mk 0)) ≫
    W.diagram.map (SimplicialObject.LeftDecalage.rightBlock.app (SimplexCategory.mk 0)).op) = _
  rw [← Category.assoc, hs, Category.assoc, ← W.diagram.map_comp, ← op_comp]
  have he : SimplicialObject.LeftDecalage.rightBlock.app (SimplexCategory.mk 0) ≫
      SimplexCategory.σ (0 : Fin 1) = 𝟙 (SimplexCategory.mk 0) := by
    ext i
    fin_cases i
    rfl
  rw [he]
  have hi : (𝟙 (SimplexCategory.mk 0)).op = 𝟙 (op (SimplexCategory.mk 0)) := rfl
  rw [hi, W.diagram.map_id, Category.comp_id]

/-- The identity section enters the actual path diagonal through its original zero row. -/
def diagonalBasepointMap (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ SSet.simplicialDiagonalFunctor.obj (diagram W x) :=
  sectionZero W x ≫
    SSet.EquifibredDiagonal.rowVertexToDiagonal (diagram W x) (SimplexCategory.mk 0) 0

/-- The same original identity-edge basepoint in the entire path diagonal. -/
def diagonalBasepoint (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (SSet.simplicialDiagonalFunctor.obj (diagram W x)) _⦋0⦌ :=
  SSet.yonedaEquiv (diagonalBasepointMap W x)

/-- The actual identity-section map projects to the original object's complete zero-row diagonal map. -/
theorem diagonalBasepointMap_projection (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    diagonalBasepointMap W x ≫ SSet.simplicialDiagonalFunctor.map (projection W x) =
      SSet.yonedaEquiv.symm x ≫
        SSet.EquifibredDiagonal.rowVertexToDiagonal W.diagram (SimplexCategory.mk 0) 0 := by
  rw [diagonalBasepointMap, Category.assoc,
    SSet.EquifibredDiagonal.rowVertexToDiagonal_naturality, ← Category.assoc,
    sectionZero_projection]

/-- The original identity-edge basepoint projects to the same original diagonal vertex. -/
theorem diagonalBasepoint_projection (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (SSet.simplicialDiagonalFunctor.map (projection W x)).app (op (SimplexCategory.mk 0))
        (diagonalBasepoint W x) = x := by
  have h := congrArg SSet.yonedaEquiv (diagonalBasepointMap_projection W x)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
    SSet.EquifibredDiagonal.rowVertexToDiagonal_app] at h
  have hc : SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0 = 𝟙 _ := by
    ext i
    fin_cases i
    rfl
  rw [hc, op_id, W.diagram.map_id] at h
  exact h

/-- The actual realized identity-edge point projects to the same original realized vertex. -/
theorem realizedBasepoint_projection (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.toTop.map (SSet.simplicialDiagonalFunctor.map (projection W x))
        (SSet.realizedVertex (diagonalBasepoint W x)) =
      SSet.realizedVertex (show (SSet.simplicialDiagonalFunctor.obj W.diagram) _⦋0⦌ from x) := by
  rw [← SSet.realizedVertex_naturality, diagonalBasepoint_projection]

/-- The whole original path diagonal has its actual weak terminal map after realization. -/
theorem diagonalTerminal_weak (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj (diagram W x)))) := by
  have ha : TopCat.weakHomotopyEquivalences (SSet.toTop.map (diagonalAugmentation W x)) :=
    diagonalAugmentation_weak W x
  let t := terminal.from (SSet.toTop.obj (Δ[0] : SSet.{u}))
  let _ : IsIso t := isIso_of_isTerminal SSet.realizedZeroIsTerminal terminalIsTerminal t
  have ht := TopCat.weakHomotopyEquivalences.comp_mem _ _ ha
    (TopCat.weakHomotopyEquivalences.of_isIso t)
  have he : SSet.toTop.map (diagonalAugmentation W x) ≫ t =
      terminal.from (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj (diagram W x))) :=
    terminal.hom_ext _ _
  rw [he] at ht
  exact ht

end SimplicialSpace.LeftDecalageObject
