/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalGroupoidLoopComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectIdentitySection

/-!
# Original edge and point readback of the path mapping-fibre comparison

All comparisons retain the complete original zero-row edge. The actual
diagonal fibre comparison uses the same original zero-row diagonal map,
and its compact-open homotopy fibre carries the constant path at the same
prescribed target object.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The whole original inverse zero-row isomorphism retains the original edge. -/
theorem zeroRowIso_inv_fst (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (zeroRowIso W x).inv ≫ (toDecalage W x).app (op (SimplexCategory.mk 0)) =
      pullback.fst (W.diagram.δ (1 : Fin 2)) (SSet.yonedaEquiv.symm x) := by
  apply (cancel_epi (zeroRowIso W x).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  exact (zeroRowIso_fst W x).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual zero-point mapping comparison keeps the full original mapping edge. -/
theorem zeroMappingFibreIso_edge (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (zeroMappingFibreIso W x y).hom ≫
        pullback.fst ((projection W x).app (op (SimplexCategory.mk 0))) (SSet.yonedaEquiv.symm y) ≫
        (toDecalage W x).app (op (SimplexCategory.mk 0)) = mappingFibre.fst W x y := by
  simp only [zeroMappingFibreIso, Iso.trans_hom, asIso_hom, pullback.map, Category.assoc,
    mappingSourceTargetIso, mappingToSourceTargetFibre]
  change (mappingToSourceTargetFibre W x y ≫
      pullback.lift (pullback.fst (sourceEdgesTarget W x) (SSet.yonedaEquiv.symm y) ≫
        (zeroRowIso W x).inv) (pullback.snd (sourceEdgesTarget W x) (SSet.yonedaEquiv.symm y) ≫ 𝟙 _) _) ≫
      pullback.fst ((projection W x).app (op (SimplexCategory.mk 0))) (SSet.yonedaEquiv.symm y) ≫
      (toDecalage W x).app (op (SimplexCategory.mk 0)) = _
  rw [Category.assoc, pullback.lift_fst_assoc, Category.assoc, zeroRowIso_inv_fst]
  unfold mappingToSourceTargetFibre
  rw [pullback.lift_fst_assoc, pullback.lift_fst]

set_option backward.isDefEq.respectTransparency false in
/-- The entire original zero-point-to-diagonal comparison retains the original zero-row diagonal leg. -/
theorem zeroPointToDiagonalFibre_fst (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    zeroPointToDiagonalFibre W x y ≫ pullback.fst (diagonalProjection W x) (diagonalPoint W y) =
      pullback.fst ((projection W x).app (op (SimplexCategory.mk 0))) (SSet.yonedaEquiv.symm y) ≫
        SSet.EquifibredDiagonal.rowVertexToDiagonal (diagram W x) (SimplexCategory.mk 0) 0 := by
  dsimp only [diagonalPoint]
  rw [zeroPointToDiagonalFibre, Category.assoc,
    (SSet.SharpPullbackClosure.nestedPullbackIso_hom_legs (diagonalProjection W x)
      (SSet.EquifibredDiagonal.rowVertexToDiagonal W.diagram (SimplexCategory.mk 0) 0)
      (SSet.yonedaEquiv.symm y)).1]
  simp only [zeroPointMap, pullback.map, ← Category.assoc, pullback.lift_fst]
  rw [Category.assoc,
    (SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison_legs
      (projection W x) (SimplexCategory.mk 0) 0).1]

/-- The original mapping-to-diagonal fibre keeps its actual zero-row object and whole diagonal leg. -/
theorem mappingToDiagonalFibre_fst (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingToDiagonalFibre W x y ≫ pullback.fst (diagonalProjection W x) (diagonalPoint W y) =
      (zeroMappingFibreIso W x y).hom ≫
        pullback.fst ((projection W x).app (op (SimplexCategory.mk 0))) (SSet.yonedaEquiv.symm y) ≫
        SSet.EquifibredDiagonal.rowVertexToDiagonal (diagram W x) (SimplexCategory.mk 0) 0 := by
  rw [mappingToDiagonalFibre, Category.assoc, zeroPointToDiagonalFibre_fst]

private theorem congrHom_second_fst {X B T : SSet.{u}} (p : X ⟶ B)
    {b c : T ⟶ B} (h : b = c) :
    (pullback.congrHom (show p = p from rfl) h).hom ≫ pullback.fst p c = pullback.fst p b := by
  subst c
  simp [pullback.congrHom_hom, pullback.map]

/-- The original vertex-point reindexing keeps the same full original total leg. -/
theorem diagonalPointFibreIso_fst (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (diagonalPointFibreIso W x y).hom ≫ pullback.fst (diagonalProjection W x)
        (SSet.yonedaEquiv.symm
          (show (SSet.simplicialDiagonalFunctor.obj W.diagram) _⦋0⦌ from y)) =
      pullback.fst (diagonalProjection W x) (diagonalPoint W y) :=
  congrHom_second_fst _ (diagonalPoint_eq_yoneda W y)

set_option backward.isDefEq.respectTransparency false in
/-- The actual compact-open homotopy-fibre comparison retains the complete original zero-row diagonal leg. -/
theorem mappingToDiagonalHomotopyFibre_toTotal (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingToDiagonalHomotopyFibre W x y ≫
        TopCat.homotopyFiberToTotal (realizedDiagonalProjection W x) (realizedDiagonalPoint W y) =
      SSet.toTop.map ((zeroMappingFibreIso W x y).hom ≫
        pullback.fst ((projection W x).app (op (SimplexCategory.mk 0))) (SSet.yonedaEquiv.symm y) ≫
        SSet.EquifibredDiagonal.rowVertexToDiagonal (diagram W x) (SimplexCategory.mk 0) 0) := by
  let yD : (SSet.simplicialDiagonalFunctor.obj W.diagram) _⦋0⦌ := y
  let bD : (Δ[0] : SSet.{u}) ⟶ SSet.simplicialDiagonalFunctor.obj W.diagram := SSet.yonedaEquiv.symm yD
  have hpt := SSet.SharpComparisonDraft.pointFibreHomotopyComparison_toTotal
    (diagonalProjection W x) bD
  change SSet.toTop.map (mappingToDiagonalFibre W x y) ≫
    (SSet.toTop.map (diagonalPointFibreIso W x y).hom ≫
      SSet.SharpComparisonDraft.pointFibreHomotopyComparison (diagonalProjection W x) bD) ≫
        TopCat.homotopyFiberToTotal (SSet.toTop.map (diagonalProjection W x)) (SSet.realizedPoint bD) = _
  have hl : SSet.toTop.map (diagonalPointFibreIso W x y).hom ≫
      SSet.SharpComparisonDraft.pointFibreHomotopyComparison (diagonalProjection W x) bD ≫
      TopCat.homotopyFiberToTotal (SSet.toTop.map (diagonalProjection W x)) (SSet.realizedPoint bD) =
    SSet.toTop.map (diagonalPointFibreIso W x y).hom ≫
      SSet.toTop.map (pullback.fst (diagonalProjection W x) bD) :=
    congrArg (fun z => SSet.toTop.map (diagonalPointFibreIso W x y).hom ≫ z) hpt
  calc
    _ = SSet.toTop.map (mappingToDiagonalFibre W x y) ≫
        (SSet.toTop.map (diagonalPointFibreIso W x y).hom ≫
          (SSet.SharpComparisonDraft.pointFibreHomotopyComparison (diagonalProjection W x) bD ≫
            TopCat.homotopyFiberToTotal (SSet.toTop.map (diagonalProjection W x)) (SSet.realizedPoint bD))) :=
      congrArg (fun z => SSet.toTop.map (mappingToDiagonalFibre W x y) ≫ z)
        (Category.assoc _ _ _)
    _ = SSet.toTop.map (mappingToDiagonalFibre W x y) ≫
        (SSet.toTop.map (diagonalPointFibreIso W x y).hom ≫
          SSet.toTop.map (pullback.fst (diagonalProjection W x) bD)) :=
      congrArg (fun z => SSet.toTop.map (mappingToDiagonalFibre W x y) ≫ z) hl
    _ = _ := by
      rw [← Functor.map_comp, diagonalPointFibreIso_fst, ← Functor.map_comp,
        mappingToDiagonalFibre_fst]

end SimplicialSpace.LeftDecalageObject
