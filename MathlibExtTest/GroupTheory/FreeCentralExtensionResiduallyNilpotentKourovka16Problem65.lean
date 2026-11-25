/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FreeCentralExtensionResiduallyNilpotentKourovka16Problem65

/-! # Tests for residual nilpotence of free central extensions -/

open MathlibExt.GroupTheory.FreeCentralExtensionResiduallyNilpotentKourovka16Problem65Wanted

-- In the infinite cyclic group, the quotient by the trivial subgroup separates every element.
example : IsResiduallyTorsionFreeNilpotent (Multiplicative ℤ) := by
  intro g hg
  refine ⟨⊥, inferInstance, hg, inferInstance, ?_⟩
  intro x hx hfin
  let e := QuotientGroup.quotientBot (G := Multiplicative ℤ)
  obtain ⟨n, hn, h⟩ := hfin.exists_pow_eq_one
  apply hx
  apply e.injective
  rw [map_one]
  apply (pow_eq_one_iff_left hn.ne').mp
  rw [← map_pow, h, map_one]

-- Extract an element of the extension that every nilpotent quotient kills.
example : ∃ (α : Type) (R : Subgroup (FreeGroup α)) (_ : R.Normal),
    let E := FreeGroup α ⧸ ⁅(⊤ : Subgroup (FreeGroup α)), R⁆
    ∃ x : E, x ≠ 1 ∧ ∀ (N : Subgroup E) [N.Normal], Group.IsNilpotent (E ⧸ N) → x ∈ N := by
  obtain ⟨α, R, hR, _, _, h⟩ := existsPresentationWithNonResiduallyNilpotentQuotient_holds
  refine ⟨α, R, hR, ?_⟩
  obtain ⟨x, hx⟩ := not_forall.mp h
  obtain ⟨hne, hsep⟩ := Classical.not_imp.mp hx
  refine ⟨x, hne, fun N inst hN => ?_⟩
  by_contra hxN
  exact hsep ⟨N, inst, hxN, hN⟩
