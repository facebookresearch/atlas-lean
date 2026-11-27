/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.RetractIntersectionFreeGroupKourovka17Problem19

namespace MathlibExt.GroupTheory.RetractIntersectionFreeGroupKourovka17Problem19Wanted

-- When H lies in R, the intersection is all of H and the identity retracts onto it.
example {G : Type*} [Group G] (R H : Subgroup G) (h : H ≤ R) :
    IsRetract ((H ⊓ R).subgroupOf H) := by
  rw [inf_eq_left.mpr h, Subgroup.subgroupOf_self]
  exact ⟨MonoidHom.id H, MonoidHom.range_eq_top.mpr Function.surjective_id, fun _ _ => rfl⟩

-- Recover the existential formulation with the intersection taken inside H.
example : ∃ (n : ℕ) (R H : Subgroup (FreeGroup (Fin n))),
    IsRetract R ∧ H.FG ∧ ¬ IsRetract ((H ⊓ R).subgroupOf H) := by
  by_contra h
  apply retractIntersectionIsRetract_refuted
  intro n R H hR hH
  by_contra hI
  exact h ⟨n, R, H, hR, hH, hI⟩

end MathlibExt.GroupTheory.RetractIntersectionFreeGroupKourovka17Problem19Wanted
