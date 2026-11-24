/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

-- BACKPORT (partially retired for Mathlib v4.34.1): Extracted from PR
-- leanprover-community/mathlib4#42435 head
-- `e09070f786c9fc0a688e6239d71230b618b045ff`, file
-- `Mathlib/AlgebraicTopology/SimplicialSet/ProdStdSimplex.lean`,
-- blob `542f70ab67214aac96e30fd0acb210d0eb3d6a64`. See `BACKPORTS.md`
-- for adaptations and upgrade-removal steps. Seven of eight declarations are
-- now upstream in pinned Mathlib `v4.34.1`
-- (`d13f23b723b8a846827a245b89c10fc7d3f11612`) at
-- `Mathlib/AlgebraicTopology/SimplicialSet/ProdStdSimplex.lean`; local copies
-- removed. `SSet.prodStdSimplex.mem_ofSimplex_obj_iff` has no upstream
-- counterpart there and is retained (original statement/proof) for downstream
-- `ProdStdSimplexOneCompat` and `SSetRealizationProductCellComparison`.

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# Product of standard simplices — partial compatibility for Lean 4.34.1

This file previously backported from PR #42435
(head `e09070f786c9fc0a688e6239d71230b618b045ff`,
file `Mathlib/AlgebraicTopology/SimplicialSet/ProdStdSimplex.lean`,
blob `542f70ab67214aac96e30fd0acb210d0eb3d6a64`, upstream author Joël Riou)
the eight declarations absent from pinned Mathlib `v4.33.0` (`db584cd`).
Seven are now upstream in pinned Mathlib `v4.34.1`
(`d13f23b723b8a846827a245b89c10fc7d3f11612`) at
`Mathlib/AlgebraicTopology/SimplicialSet/ProdStdSimplex.lean` with identical
statements; local copies removed.

## Upstream replacements (pinned Mathlib v4.34.1)

* `SSet.prodStdSimplex.objEquiv_apply_symm_apply` (`@[simp]`, `rfl`)
* `SSet.prodStdSimplex.isoNerve_hom_app_obj` (`rfl`)
* `SSet.prodStdSimplex.range_isoNerve_hom_app_obj`
* `SSet.prodStdSimplex.ofSimplex_le_ofSimplex_iff`
* private `SSet.prodStdSimplex.exists_nonDegenerate_max_dim_aux`
* `SSet.prodStdSimplex.exists_nonDegenerate_max_dim`
* `SSet.prodStdSimplex.subcomplex_eq_top_iff`

Verification: names, hypotheses, universes (`u`), and conclusions match
byte-for-byte against the pinned upstream file; proofs differ only by
4.33-pin adaptations now obsolete (`Subcomplex.mem_ofSimplex_obj_iff` vs
`stdSimplex.mem_ofSimplex_obj_iff` in the auxiliary, `.2` vs `.mpr` in
`subcomplex_eq_top_iff`). Supporting `Fin` (`Mathlib.Order.Fin.Prod`,
`Mathlib.Order.Fin.InsertNth`), `SSet.Subcomplex.image_le_image_iff`, and
`PartialOrder.nerve_ofSimplex_le_ofSimplex_iff` are all upstream, so the
local compatibility imports were replaced by the single canonical import
above (transitively re-exported for downstream).

## Retained declaration

* `SSet.prodStdSimplex.mem_ofSimplex_obj_iff` — no upstream counterpart in
  the pinned `ProdStdSimplex.lean` (only `stdSimplex.mem_ofSimplex_obj_iff`
  and generic `Subcomplex.mem_ofSimplex_obj_iff` exist). Retained verbatim
  (statement and `rw [← Subcomplex.ofSimplex_le_iff,
  ofSimplex_le_ofSimplex_iff]` proof, now via upstream
  `ofSimplex_le_ofSimplex_iff`) because downstream
  `MathlibExt.AlgebraicTopology.SimplicialSet.ProdStdSimplexOneCompat`
  and `SimplicialRealization.PointSet.SSetRealizationProductCellComparison`
  still use it. Do not add wrappers, instances, or new API here.

## Removal rule

Delete this module
`MathlibExt/AlgebraicTopology/SimplicialSet/ProdStdSimplexCompat.lean` and
switch any imports of it to
`Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex` once pinned Mathlib
provides `mem_ofSimplex_obj_iff` upstream or downstream no longer uses it;
regenerate `MathlibExt.lean` in a separate Avocado task. Durable ledger is
tracked in `BACKPORTS.md`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Simplicial
open scoped Simplicial

namespace SSet

namespace prodStdSimplex

variable {p q : ℕ}

lemma mem_ofSimplex_obj_iff
    {n m : ℕ} (s : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (t : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋m⦌) :
    s ∈ (Subcomplex.ofSimplex t).obj _ ↔
      Set.range (objEquiv s) ⊆ Set.range (objEquiv t) := by
  rw [← Subcomplex.ofSimplex_le_iff, ofSimplex_le_ofSimplex_iff]

end prodStdSimplex

end SSet
