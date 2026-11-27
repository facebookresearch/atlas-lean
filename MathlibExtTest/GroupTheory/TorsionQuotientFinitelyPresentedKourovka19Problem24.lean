/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.TorsionQuotientFinitelyPresentedKourovka19Problem24

/-! # Tests for `MathlibExt.GroupTheory.TorsionQuotientFinitelyPresentedKourovka19Problem24` -/

open MathlibExt.GroupTheory.TorsionQuotientFinitelyPresentedKourovka19Problem24Wanted

-- The theorem with `torsionClosure` unfolded.
example : ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧
    ¬ Group.IsFinitelyPresented (G ⧸ Subgroup.normalClosure {g : G | IsOfFinOrder g}) :=
  existsFinitelyPresentedTorsionQuotientNotFinitelyPresented_holds

-- A witness must have torsion: the quotient by the trivial subgroup is finitely presented.
example : ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ torsionClosure G ≠ ⊥ := by
  obtain ⟨G, _, hG, hQ⟩ := existsFinitelyPresentedTorsionQuotientNotFinitelyPresented_holds
  exact ⟨G, _, hG, fun h =>
    hQ (Group.IsFinitelyPresented.quotient _ (h ▸ Subgroup.IsFinitelyNormallyGenerated.bot))⟩

-- In a finite group every element has finite order, so the torsion closure is everything.
example (G : Type) [Group G] [Finite G] : torsionClosure G = ⊤ :=
  eq_top_iff.mpr fun g _ => Subgroup.subset_normalClosure (isOfFinOrder_of_finite g)

-- In the torsion-free group `ℤ` the torsion closure is trivial.
example : torsionClosure (Multiplicative ℤ) = ⊥ := by
  refine le_bot_iff.mp (Subgroup.normalClosure_le_normal fun g hg => ?_)
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
  have h' : (n : ℤ) * g.toAdd = 0 := by rw [← nsmul_eq_mul, ← toAdd_pow, h, toAdd_one]
  have hg' : g.toAdd = 0 := (mul_eq_zero.mp h').resolve_left (by exact_mod_cast hn.ne')
  simpa [Subgroup.mem_bot] using congrArg Multiplicative.ofAdd hg'
