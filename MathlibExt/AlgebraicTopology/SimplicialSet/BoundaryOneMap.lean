/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc

/-!
# Maps from the boundary of the one-simplex

A pair of vertices of a simplicial set determines a map from the finite
nonsingular two-point simplicial set `∂Δ[1]`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

/-- The map from the boundary of the one-simplex classified by two vertices. -/
noncomputable def boundaryOneMap {Y : SSet.{u}}
    (x₀ x₁ : Y _⦋0⦌) :
    (∂Δ[1] : SSet.{u}) ⟶ Y := by
  let faces : Fin 2 → ((Δ[0] : SSet.{u}) ⟶ Y) :=
    fun j => if j = 0 then SSet.const x₁ else SSet.const x₀
  have hfaces : SSet.boundary.IsCompatible faces := by
    rw [SSet.boundary.isCompatible_zero_iff_true]
    trivial
  exact hfaces.desc

/-- Face `1` is sent to the first selected vertex. -/
@[simp]
theorem boundary_ι_one_boundaryOneMap {Y : SSet.{u}}
    (x₀ x₁ : Y _⦋0⦌) :
    SSet.boundary.ι (1 : Fin 2) ≫ boundaryOneMap x₀ x₁ =
      SSet.const x₀ := by
  rw [boundaryOneMap, SSet.boundary.IsCompatible.ι_desc]
  simp

/-- Face `0` is sent to the second selected vertex. -/
@[simp]
theorem boundary_ι_zero_boundaryOneMap {Y : SSet.{u}}
    (x₀ x₁ : Y _⦋0⦌) :
    SSet.boundary.ι (0 : Fin 2) ≫ boundaryOneMap x₀ x₁ =
      SSet.const x₁ := by
  rw [boundaryOneMap, SSet.boundary.IsCompatible.ι_desc]
  simp

end SSet

end
