/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.DerivedSubgroupInclusionFreeGroupKourovka13Problem62

namespace MathlibExt.GroupTheory.DerivedSubgroupInclusionFreeGroupKourovka13Problem62Wanted

/-- The refutation supplies an element separating two non-cyclic subgroups with nested
derived subgroups, as in the existential formulation of the problem. -/
example : ∃ (α : Type) (U V : Subgroup (FreeGroup α)), ¬ IsCyclic U ∧ ¬ IsCyclic V ∧
    ⁅U, U⁆ ≤ ⁅V, V⁆ ∧ ∃ x ∈ U, x ∉ V := by
  by_contra h
  apply derivedInclusionImpliesInclusion_refuted
  intro α U V hU hV hUV x hx
  by_contra hxV
  exact h ⟨α, U, V, hU, hV, hUV, x, hx, hxV⟩

end MathlibExt.GroupTheory.DerivedSubgroupInclusionFreeGroupKourovka13Problem62Wanted
