/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ScottishBook62
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.NormNum.GCD

/-! # Tests for `MathlibExt.GroupTheory.ScottishBook62` -/

namespace MathlibExtTest.ScottishBook62

open scoped Nat
open AddSubgroup MathlibExt.GroupTheory.ScottishBook62Wanted

-- Test section: the subgroups `(1 / N) ℤ` of `ℚ`. Membership depends on divisibility, not size:
-- `5 / 6` lies in `(1 / 3!) ℤ` although its denominator `6` exceeds `3`.
example : (5 / 6 : ℚ) ∈ zmultiples ((3 ! : ℚ)⁻¹) :=
  (mem_zmultiples_inv_natCast_iff (Nat.factorial_ne_zero 3)).2 (by norm_num [Nat.factorial])

-- `1 / 4` lies in `(1 / 4!) ℤ` but not in `(1 / 3!) ℤ`, so the chain does not stop growing at `3`.
example : (1 / 4 : ℚ) ∉ zmultiples ((3 ! : ℚ)⁻¹) ∧ (1 / 4 : ℚ) ∈ zmultiples ((4 ! : ℚ)⁻¹) := by
  simp only [mem_zmultiples_inv_natCast_iff (Nat.factorial_ne_zero _)]
  norm_num [Nat.factorial]

-- The hypothesis `N ≠ 0` is needed: `(0 : ℚ)⁻¹ = 0`, so `zmultiples (0 : ℚ)⁻¹` is `⊥`, which misses
-- `1 / 2` although every denominator divides `0`.
example : (1 / 2 : ℚ) ∉ zmultiples (((0 : ℕ) : ℚ)⁻¹) ∧ (1 / 2 : ℚ).den ∣ 0 := by
  simp

-- The chain starts with `H 0 = H 1 = ℤ`, since `0! = 1! = 1`.
example : zmultiples ((0 ! : ℚ)⁻¹) = zmultiples ((1 ! : ℚ)⁻¹) := by
  simp

-- Monotonicity applies across several steps.
example : zmultiples ((2 ! : ℚ)⁻¹) ≤ zmultiples ((5 ! : ℚ)⁻¹) :=
  monotone_zmultiples_inv_factorial (by norm_num)

-- The supremum is the union: every rational number lies in some `(1 / n!) ℤ`.
example (x : ℚ) : ∃ n : ℕ, x ∈ zmultiples ((n ! : ℚ)⁻¹) :=
  (mem_iSup_of_directed monotone_zmultiples_inv_factorial.directed_le).1
    (iSup_zmultiples_inv_factorial ▸ mem_top x)

-- Test section: `ℚ` is isomorphic neither to `ℤ`, nor to a finite cyclic group, nor to any of its
-- own cyclic subgroups.
example : IsEmpty (ℚ ≃+ ℤ) :=
  isEmpty_rat_addEquiv

example : IsEmpty (ℚ ≃+ ZMod 6) :=
  isEmpty_rat_addEquiv

example (q : ℚ) : IsEmpty (ℚ ≃+ zmultiples q) :=
  isEmpty_rat_addEquiv

-- Test section: the claim and its refutation. A constant chain satisfies the hypotheses and the
-- conclusion of the claim together, so refuting the claim needs a genuine counterexample.
example (G : Type) [AddCommGroup G] :
    let H : ℕ → AddSubgroup G := fun _ ↦ ⊤
    (∀ n, H n ≤ H (n + 1)) ∧ (∀ n, Nonempty (H n ≃+ H 1)) ∧ (⨆ n, H n) = ⊤ ∧
      Nonempty (G ≃+ H 1) :=
  ⟨fun _ ↦ le_rfl, fun _ ↦ ⟨AddEquiv.refl _⟩, iSup_const, ⟨topEquiv.symm⟩⟩

-- The refutation yields an explicit counterexample: an abelian group that is the union of an
-- increasing chain of subgroups isomorphic to `H 1` but is not isomorphic to `H 1`.
example : ∃ (G : Type) (_ : AddCommGroup G) (H : ℕ → AddSubgroup G),
    (∀ n, H n ≤ H (n + 1)) ∧ (∀ n, Nonempty (H n ≃+ H 1)) ∧ (⨆ n, H n) = ⊤ ∧
      IsEmpty (G ≃+ H 1) := by
  by_contra h
  refine mazurUlam62_refuted fun G _ H h1 h2 h3 ↦ ?_
  by_contra h4
  exact h ⟨G, _, H, h1, h2, h3, not_nonempty_iff.1 h4⟩

end MathlibExtTest.ScottishBook62
