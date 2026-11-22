/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontPointedDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontUniversalMap

/-!
# The SAME full original fixed-front boundary readbacks

The entire original front projects to its structural source, and the
original right vertex projects to the original target. Every map in the
endpoint-fixed category retains these SAME source and target images.
These are full source equations used by the original right-mapping
resolution, with no weak or fibrancy outcome assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- Every complete original front simplex projects to the SAME structural source in its original scalar degree. -/
theorem projection_front_const (n : ℕ) :
    SSet.frontInclusion n ≫ FixedFrontCollapse.projection.{u} n =
      SSet.const (X := (Δ[n] : SSet.{u})) (FixedFrontCollapse.source n) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  let v : (Δ[n + 1] : SSet.{u}) _⦋0⦌ :=
    SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0)
  let θ : op ⦋0⦌ ⟶ op ⦋d⦌ := (SimplexCategory.const ⦋d⦌ ⦋0⦌ 0).op
  have hfront : FixedFrontCollapse.InFront ((SSet.frontInclusion n).app (op ⦋d⦌) a) := by
    have he := congrArg (fun f => f.app (op ⦋d⦌) a) (SSet.frontInclusion_eq.{u} n)
    rw [he]
    intro i
    change (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom (a.down.toOrderHom i) ≠ Fin.last (n + 1)
    exact (Fin.succAbove_last_apply _).trans_ne (ne_of_lt (Fin.castSucc_lt_last _))
  have hv : FixedFrontCollapse.InFront v :=
    FixedFrontVertices.constant_front 0 (ne_of_lt Fin.last_pos)
  exact FixedFrontCollapse.projection_front_eq _ _ hfront (FixedFrontCollapse.inFront_map θ v hv)

/-- Every SAME original endpoint-fixed map retains its literal original source and target vertex images. -/
theorem pointedHom_vertices {K : SSet.{u}} (x y : K _⦋0⦌) {n : ℕ}
    (g : pointedObject.{u} n ⟶ Under.mk (SSet.boundaryOneMap x y)) :
    g.right.app (op ⦋0⦌) (FixedFrontCollapse.source n) = x ∧
      g.right.app (op ⦋0⦌) (FixedFrontCollapse.target n) = y := by
  have hs := congrArg (fun f => SSet.boundary.ι (1 : Fin 2) ≫ f) (Under.w g)
  have ht := congrArg (fun f => SSet.boundary.ι (0 : Fin 2) ≫ f) (Under.w g)
  have hS : SSet.const (X := (Δ[0] : SSet.{u})) (FixedFrontCollapse.source n) ≫ g.right = SSet.const x := by
    exact (congrArg (fun f => f ≫ g.right)
      (SSet.boundary_ι_one_boundaryOneMap (FixedFrontCollapse.source n) (FixedFrontCollapse.target n))).symm.trans
        ((Category.assoc _ _ _).trans (hs.trans (SSet.boundary_ι_one_boundaryOneMap x y)))
  have hT : SSet.const (X := (Δ[0] : SSet.{u})) (FixedFrontCollapse.target n) ≫ g.right = SSet.const y := by
    exact (congrArg (fun f => f ≫ g.right)
      (SSet.boundary_ι_zero_boundaryOneMap (FixedFrontCollapse.source n) (FixedFrontCollapse.target n))).symm.trans
        ((Category.assoc _ _ _).trans (ht.trans (SSet.boundary_ι_zero_boundaryOneMap x y)))
  constructor
  · have he := (SSet.const_comp (FixedFrontCollapse.source n) g.right).symm.trans hS
    exact (SSet.yonedaEquiv_const _).symm.trans
      ((congrArg SSet.yonedaEquiv he).trans (SSet.yonedaEquiv_const _))
  · have he := (SSet.const_comp (FixedFrontCollapse.target n) g.right).symm.trans hT
    exact (SSet.yonedaEquiv_const _).symm.trans
      ((congrArg SSet.yonedaEquiv he).trans (SSet.yonedaEquiv_const _))

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
