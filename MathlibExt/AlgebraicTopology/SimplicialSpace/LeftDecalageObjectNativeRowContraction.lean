/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeHomotopyCut
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeCutOrdinal
import MathlibExt.AlgebraicTopology.SimplicialSpace.DiagonalMappingFibreCylinder

/-!
# The actual row-zero native path contraction and original edge interval

Restrict the original native diagonal contraction to the original zero-row
path object and project it to the original diagonal. Its entire interval
formula is the same whole original edge evaluation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The original row-zero path object enters its entire diagonal by its literal original constant operator. -/
abbrev pathZeroToDiagonal (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :=
  SSet.EquifibredDiagonal.rowVertexToDiagonal (diagram W x) (SimplexCategory.mk 0) 0

set_option backward.isDefEq.respectTransparency false in
/-- Projecting the actual original zero-row native contraction retains the complete original edge interval. -/
theorem nativeRowZeroContraction_projection (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (pathZeroToDiagonal W x ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫ (nativeDiagonalContraction W x).h ≫
        SSet.simplicialDiagonalFunctor.map (projection W x) =
      ((toDecalage W x).app (op (SimplexCategory.mk 0)) ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫
        SSet.EquifibredDiagonal.rowSimplexEvaluation W.diagram (SimplexCategory.mk 1) := by
  apply NatTrans.ext
  funext e
  induction e using Opposite.rec with
  | _ e =>
    induction e using SimplexCategory.rec with
    | _ n =>
      apply ConcreteCategory.hom_ext
      intro z
      rcases z with ⟨z, t⟩
      obtain ⟨j, rfl⟩ := SSet.stdSimplex.objMk₁_surjective t
      induction j using Fin.cases with
      | zero =>
        change ((projection W x).app (op (SimplexCategory.mk n))).app (op (SimplexCategory.mk n))
          ((nativeDiagonalContraction W x).h.app (op (SimplexCategory.mk n))
            ((pathZeroToDiagonal W x).app (op (SimplexCategory.mk n)) z, SSet.stdSimplex.objMk₁ 0)) = _
        rw [nativeDiagonalContraction_cut_zero]
        simp only [pathZeroToDiagonal, SSet.EquifibredDiagonal.rowVertexToDiagonal_app,
          ]
        have hn := types_congr_hom (congrArg (fun q => q.app (op (SimplexCategory.mk n)))
          ((projection W x).naturality (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0).op)) z
        change ((projection W x).app (op (SimplexCategory.mk n))).app (op (SimplexCategory.mk n))
            (((diagram W x).map (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0).op).app
              (op (SimplexCategory.mk n)) z) =
          (W.diagram.map (SSet.stdSimplex.objEquiv (SSet.stdSimplex.objMk₁ (0 : Fin (n + 2)))).op).app
            (op (SimplexCategory.mk n)) (((toDecalage W x).app (op (SimplexCategory.mk 0))).app
              (op (SimplexCategory.mk n)) z)
        have hc : SSet.stdSimplex.objEquiv (SSet.stdSimplex.objMk₁.{u} (0 : Fin (n + 2))) =
            SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 1) 1 := by
          ext j
          rfl
        rw [hc]
        have hconst : (projection W x).app (op (SimplexCategory.mk 0)) ≫
            W.diagram.map (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0).op =
          (toDecalage W x).app (op (SimplexCategory.mk 0)) ≫
            W.diagram.map (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 1) 1).op := by
          change ((toDecalage W x).app (op (SimplexCategory.mk 0)) ≫
            W.diagram.map (SimplicialObject.LeftDecalage.rightBlock.app (SimplexCategory.mk 0)).op) ≫ _ = _
          rw [Category.assoc, ← W.diagram.map_comp, ← op_comp]
          congr 2
        have h0 := types_congr_hom (congrArg (fun q => q.app (op (SimplexCategory.mk n))) hconst) z
        exact hn.trans h0
      | succ i =>
        change ((projection W x).app (op (SimplexCategory.mk n))).app (op (SimplexCategory.mk n))
          ((nativeDiagonalContraction W x).h.app (op (SimplexCategory.mk n))
            ((pathZeroToDiagonal W x).app (op (SimplexCategory.mk n)) z, SSet.stdSimplex.objMk₁ i.succ)) = _
        rw [nativeDiagonalContraction_cut_succ]
        simp only [pathZeroToDiagonal, SSet.EquifibredDiagonal.rowVertexToDiagonal_app]
        have hface := nativeHomotopyFace_fst W x n i
        have hnat := (toDecalage W x).naturality (SimplexCategory.δ i.succ).op
        have hrow := (toDecalage W x).naturality
          (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0).op
        have hc := nativeHomotopyOrdinal_row_zero n i
        change (((diagram W x).map (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0).op ≫
          (extraDegeneracy W x).homotopy.h i ≫ (diagram W x).δ i.succ ≫
          (projection W x).app (op (SimplexCategory.mk n))).app (op (SimplexCategory.mk n))) z = _
        change (((diagram W x).map (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0).op ≫
          (extraDegeneracy W x).homotopy.h i ≫ (diagram W x).map (SimplexCategory.δ i.succ).op ≫
          (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
          W.diagram.map (SimplicialObject.LeftDecalage.rightBlock.app (SimplexCategory.mk n)).op).app
            (op (SimplexCategory.mk n))) z = _
        let H : (diagram W x).obj (op (SimplexCategory.mk n)) ⟶
            (diagram W x).obj (op (SimplexCategory.mk (n + 1))) := (extraDegeneracy W x).homotopy.h i
        change H ≫ (toDecalage W x).app (op (SimplexCategory.mk (n + 1))) =
          (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
            W.diagram.map (nativeHomotopyOrdinal n i).op at hface
        have heq : (diagram W x).map (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0).op ≫
            H ≫ (diagram W x).map (SimplexCategory.δ i.succ).op ≫
              (toDecalage W x).app (op (SimplexCategory.mk n)) =
          (toDecalage W x).app (op (SimplexCategory.mk 0)) ≫
            (SimplicialObject.LeftDecalage.diagram W.diagram).map
              (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0).op ≫
            W.diagram.map (nativeHomotopyOrdinal n i).op ≫
            (SimplicialObject.LeftDecalage.diagram W.diagram).map (SimplexCategory.δ i.succ).op := by
          dsimp only [nativeHomotopyOrdinal] at hface ⊢
          rw [hnat]
          have hf := congrArg (fun q =>
            (diagram W x).map (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0).op ≫ q ≫
              (SimplicialObject.LeftDecalage.diagram W.diagram).map (SimplexCategory.δ i.succ).op) hface
          simp only [Category.assoc] at hf ⊢
          rw [hf, ← Category.assoc, hrow]
          simp only [Category.assoc]
        have heval := types_congr_hom (congrArg (fun q => q.app (op (SimplexCategory.mk n)))
          (congrArg (fun q => q ≫ W.diagram.map
            (SimplicialObject.LeftDecalage.rightBlock.app (SimplexCategory.mk n)).op) heq)) z
        simp only [Category.assoc] at heval
        change (((diagram W x).map (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0).op ≫
          H ≫ (diagram W x).map (SimplexCategory.δ i.succ).op ≫
          (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
          W.diagram.map (SimplicialObject.LeftDecalage.rightBlock.app (SimplexCategory.mk n)).op).app
            (op (SimplexCategory.mk n))) z = _
        rw [heval]
        change (((toDecalage W x).app (op (SimplexCategory.mk 0)) ≫
          W.diagram.map (SimplicialObject.LeftDecalage.ordinal.map
            (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0)).op ≫
          W.diagram.map (nativeHomotopyOrdinal n i).op ≫
          W.diagram.map (SimplicialObject.LeftDecalage.ordinal.map (SimplexCategory.δ i.succ)).op ≫
          W.diagram.map (SimplicialObject.LeftDecalage.rightBlock.app (SimplexCategory.mk n)).op).app
            (op (SimplexCategory.mk n))) z = _
        rw [← W.diagram.map_comp, ← W.diagram.map_comp, ← W.diagram.map_comp,
          ← op_comp, ← op_comp, ← op_comp]
        simp only [Category.assoc]
        rw [hc]
        rfl

end SimplicialSpace.LeftDecalageObject
