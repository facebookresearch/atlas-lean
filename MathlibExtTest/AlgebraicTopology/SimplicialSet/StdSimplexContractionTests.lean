/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexContraction

/-!
# Standard-simplex contraction tests

These tests pin the arbitrary-time contraction formula on a genuine crossing
interval simplex.  The selected edge of `Δ[2]` has vertices `0, 1`, while the
cylinder sends its second vertex to the last vertex `2`.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.StdSimplexContractionTests

/-- The identity `1`-simplex of `Δ[1]`, whose time values cross from `0` to
`1`. -/
private def crossingTime :
    (Δ[1] : SSet.{u}).obj (op ⦋1⦌) :=
  SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)

/-- The edge `0 → 1` of `Δ[2]`, represented by the coface omitting vertex
`2`. -/
private def edgeZeroOne :
    (Δ[2] : SSet.{u}).obj (op ⦋1⦌) :=
  SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.δ (2 : Fin 3))

/-- The selected interval simplex genuinely contains a `0 → 1` crossing. -/
example :
    crossingTime.{u} (0 : Fin 2) = 0 ∧
      crossingTime.{u} (1 : Fin 2) = 1 :=
  ⟨rfl, rfl⟩

/-- The contraction retains the first vertex at crossing time. -/
example :
    SSet.stdSimplex.asOrderHom
        ((SSet.stdSimplex.homotopyIdConstLast.{u} 2).h.app (op ⦋1⦌)
          ⟨edgeZeroOne.{u}, crossingTime.{u}⟩) (0 : Fin 2) = 0 := by
  rw [SSet.stdSimplex.homotopyIdConstLast_h_app_apply]
  rfl

/-- At the other end of the crossing, the original vertex `1` is replaced by
the last vertex `2`. -/
example :
    SSet.stdSimplex.asOrderHom
        ((SSet.stdSimplex.homotopyIdConstLast.{u} 2).h.app (op ⦋1⦌)
          ⟨edgeZeroOne.{u}, crossingTime.{u}⟩) (1 : Fin 2) = Fin.last 2 ∧
      edgeZeroOne.{u} (1 : Fin 2) = (1 : Fin 3) := by
  constructor
  · rw [SSet.stdSimplex.homotopyIdConstLast_h_app_apply]
    rfl
  · rfl

/-- Pointwise monotonicity is available for every degree, simplex, and time. -/
example (n : ℕ) (a : SimplexCategoryᵒᵖ)
    (α : (Δ[n] : SSet.{u}).obj a)
    (t : (Δ[1] : SSet.{u}).obj a) :
    ∀ i : Fin (a.unop.len + 1),
      SSet.stdSimplex.asOrderHom α i ≤
        SSet.stdSimplex.asOrderHom
          ((SSet.stdSimplex.homotopyIdConstLast.{u} n).h.app a ⟨α, t⟩) i :=
  SSet.stdSimplex.le_homotopyIdConstLast_h_app_apply n a α t

end MathlibExtTest.AlgebraicTopology.SimplicialSet.StdSimplexContractionTests

end
