/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Arithmetic degree transport for pointed joins

The identification `SSet.zeroAddSuccIso` transports the ordinal degree
`0 + n + 1` to `n + 1` while preserving every vertex index in both
directions. It is shared by join computations and horn descent.
-/

@[expose] public section

noncomputable section
open CategoryTheory
open scoped Simplicial

namespace SSet

/-- The simplex-category identification `⦋0 + n + 1⦌ ≅ ⦋n + 1⦌`
induced by the cast on vertices. -/
def zeroAddSuccIso (n : ℕ) : ⦋0 + n + 1⦌ ≅ ⦋n + 1⦌ :=
  eqToIso (SimplexCategory.ext (by simp))

/-- The forward map of `SSet.zeroAddSuccIso` preserves vertex
indices. -/
@[simp]
lemma zeroAddSuccIso_hom_toOrderHom_val {n : ℕ} (i : Fin (0 + n + 1 + 1)) :
    ((zeroAddSuccIso n).hom.toOrderHom i).val = i.val := by
  have h : ⦋0 + n + 1⦌ = ⦋n + 1⦌ := SimplexCategory.ext (by simp)
  change ((eqToHom h).toOrderHom i).val = i.val
  rw [SimplexCategory.eqToHom_toOrderHom]
  rfl

/-- The inverse map of `SSet.zeroAddSuccIso` preserves vertex
indices. -/
@[simp]
lemma zeroAddSuccIso_inv_toOrderHom_val {n : ℕ} (i : Fin (n + 1 + 1)) :
    ((zeroAddSuccIso n).inv.toOrderHom i).val = i.val := by
  have h : ⦋n + 1⦌ = ⦋0 + n + 1⦌ := SimplexCategory.ext (by simp)
  change ((eqToHom h).toOrderHom i).val = i.val
  rw [SimplexCategory.eqToHom_toOrderHom]
  rfl

end SSet
