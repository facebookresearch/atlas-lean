/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.WeightedBarData

/-!
# Strict ordinary weighted bar as a simplicial object

This module packages the weighted-bar data `wbarData` as a genuine
simplicial object via `Data.toSimplicialObject`, with stable object/face/
degeneracy computations.

Nonclaims: no `GenRel` internals, no augmented
objects, no comparisons, no enriched copowers/coends, and no
realization/homotopy-colimit or model-category conclusion. Separate
diagram/weight functoriality and the mixed square are in `WeightedBarMapF` /
`WeightedBarMapW` / `WeightedBarMapFW`; their categorical packaging is in
`WeightedBarFunctor`.
-/

@[expose] public section

namespace CategoryTheory
namespace StrictOrdinaryWeightedBar

universe vJ uJ vC uC uW

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C)
variable [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]

/-- The strict ordinary weighted bar as a genuine simplicial object. -/
noncomputable def wbarSimplicial : SimplicialObject C :=
  (wbarData W F).toSimplicialObject

/-- Degree computation for the bundled simplicial object. -/
@[simp]
theorem wbarSimplicial_obj_mk (n : ℕ) :
    (wbarSimplicial W F).obj (Opposite.op (SimplexCategory.mk n)) =
      wbarObj W F n :=
  rfl

/-- Face computation for the bundled simplicial object. -/
theorem wbarSimplicial_map_δ {n : ℕ} (i : Fin (n + 2)) :
    (wbarSimplicial W F).map (SimplexCategory.δ i).op =
      wbarδ W F n i := by
  unfold wbarSimplicial
  rw [SimplicialObject.Data.toSimplicialObject_map_δ, wbarData_δ]

/-- Degeneracy computation for the bundled simplicial object. -/
theorem wbarSimplicial_map_σ {n : ℕ} (i : Fin (n + 1)) :
    (wbarSimplicial W F).map (SimplexCategory.σ i).op =
      wbarσ W F n i := by
  unfold wbarSimplicial
  rw [SimplicialObject.Data.toSimplicialObject_map_σ, wbarData_σ]

end StrictOrdinaryWeightedBar
end CategoryTheory
