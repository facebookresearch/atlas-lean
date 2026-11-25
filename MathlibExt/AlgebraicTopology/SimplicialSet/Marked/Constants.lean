/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Basic

/-!
# Constant maps of original marked simplicial sets

The native constant simplicial map preserves every marking because each
image edge is the actual degenerate edge at its chosen original vertex.
No condition on the source marking or a marked model structure is used.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

private theorem constant_one_eq_sigma :
    SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 = SimplexCategory.σ (0 : Fin 1) := by
  ext i
  fin_cases i <;> rfl

/-- The original constant simplicial map is a marked map for every chosen target vertex. -/
def const {X Y : Marked.{u}} (y : Y.toSSet _⦋0⦌) : X ⟶ Y where
  hom := SSet.const y
  preserve _ := by
    change Y.toSSet.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op y ∈ Y.marking
    rw [constant_one_eq_sigma]
    change Y.toSSet.σ (0 : Fin 1) y ∈ Y.marking
    exact Y.degenerate_mem y

/-- Forgetting the constant marking retains the complete original constant map. -/
@[simp]
theorem const_hom {X Y : Marked.{u}} (y : Y.toSSet _⦋0⦌) : (const (X := X) y).hom = SSet.const y := rfl

/-- The same original constant edge is the actual degeneracy of the chosen vertex. -/
theorem const_app_one {X Y : Marked.{u}} (y : Y.toSSet _⦋0⦌) (e : X.toSSet _⦋1⦌) :
    (const (X := X) y).hom.app (op ⦋1⦌) e = Y.toSSet.σ (0 : Fin 1) y := by
  change Y.toSSet.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op y = Y.toSSet.σ (0 : Fin 1) y
  rw [constant_one_eq_sigma]
  rfl

end SSet.Marked
