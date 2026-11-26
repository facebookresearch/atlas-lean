/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ElementaryAmenableVirtuallySolvable

/-! # Tests for elementary amenability and virtual solvability -/

namespace MathlibExtTest.GroupTheory.ElementaryAmenableVirtuallySolvable

open MathlibExt.GroupTheory.ElementaryAmenableVirtuallySolvableKourovka16Problem52Wanted

-- The finite symmetric group on five letters is nonsolvable and still has a solvable
-- finite-index subgroup, so it cannot serve as the counterexample.
example : IsElementaryAmenable (Equiv.Perm (Fin 5)) ∧
    ¬ Group.IsSolvable (Equiv.Perm (Fin 5)) ∧
    ∃ N : Subgroup (Equiv.Perm (Fin 5)), N.FiniteIndex ∧ Group.IsSolvable N :=
  ⟨.of_finite _, Equiv.Perm.not_isSolvable_fin_5, ⊥, inferInstance, inferInstance⟩

-- Extract the counterexample in existential form, keeping both hypotheses on the group.
example : ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ IsElementaryAmenable G ∧
    ∀ N : Subgroup G, N.FiniteIndex → ¬ Group.IsSolvable N := by
  by_contra! h
  exact finitelyPresentedElementaryAmenableVirtuallySolvable_refuted h

end MathlibExtTest.GroupTheory.ElementaryAmenableVirtuallySolvable
