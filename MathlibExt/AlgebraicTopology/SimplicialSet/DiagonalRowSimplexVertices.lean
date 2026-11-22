/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.DiagonalRowSimplexEvaluation

/-!
# The original vertex restrictions of the whole row-simplex evaluation

Every original vertex inclusion restricts the same row-simplex evaluation
to the existing row-vertex-to-diagonal map, retaining the complete row
element and the original constant ordinal operator in every scalar degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.EquifibredDiagonal

/-- The original vertex of the ordinal simplex as its whole representable point map. -/
def rowSimplexVertex (n : SimplexCategory) (v : Fin (n.len + 1)) :
    (Δ[0] : SSet.{u}) ⟶ SSet.stdSimplex.obj n :=
  SSet.stdSimplex.map (SimplexCategory.const (SimplexCategory.mk 0) n v)

/-- Every original vertex restriction is the same original row-vertex-to-diagonal map. -/
theorem rowSimplexEvaluation_vertex (W : SimplicialObject SSet.{u})
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    (𝟙 (W.obj (op n)) ⊗ₘ rowSimplexVertex n v) ≫ rowSimplexEvaluation W n =
      CartesianMonoidalCategory.fst (W.obj (op n)) (Δ[0] : SSet.{u}) ≫
        rowVertexToDiagonal W n v := by
  apply NatTrans.ext
  funext e
  apply ConcreteCategory.hom_ext
  intro z
  rcases z with ⟨x, t⟩
  change (W.map (SSet.stdSimplex.objEquiv ((rowSimplexVertex n v).app e t)).op).app e x =
    (rowVertexToDiagonal W n v).app e x
  rw [rowVertexToDiagonal_app]
  have hc : SSet.stdSimplex.objEquiv ((rowSimplexVertex n v).app e t) =
      SimplexCategory.const e.unop n v := by
    change SSet.stdSimplex.objEquiv t ≫
      SimplexCategory.const (SimplexCategory.mk 0) n v = _
    exact constant_precomp _ v
  rw [hc]
  rfl

end SSet.EquifibredDiagonal
