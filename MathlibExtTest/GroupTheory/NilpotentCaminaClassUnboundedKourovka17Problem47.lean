/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.GroupTheory.NilpotentCaminaClassUnboundedKourovka17Problem47

/-! # Tests for the nilpotent Camina-type groups of unbounded class -/

namespace MathlibExtTest.GroupTheory.NilpotentCaminaClassUnboundedKourovka17Problem47

open MathlibExt.GroupTheory.NilpotentCaminaClassUnboundedKourovka17Problem47Wanted
open commutatorElement

/-- The refutation, with the proposition unfolded as in the source. -/
private theorem exactSource :
    ¬ ∃ c : ℕ, ∀ (G : Type) [Group G], Group.IsNilpotent G →
      (∀ x : G, x ∉ commutator G →
        ∀ y : G, (∃ z ∈ commutator G, y = x * z) ↔ ∃ g : G, y = g * x * g⁻¹) →
      Group.nilpotencyClass G ≤ c :=
  nilpotentCaminaClassBounded_refuted

/-- Over the algebraic closure of `ZMod 2`, the group of `(c + 2) × (c + 2)` matrices has
nilpotency class exactly `c + 1`: the construction attains every positive class. -/
example (c : ℕ) :
    Group.nilpotencyClass
      (caminaGroup (frobenius (AlgebraicClosure (ZMod 2)) 2) (c + 1)) = c + 1 := by
  have := isNilpotent (frobenius (AlgebraicClosure (ZMod 2)) 2) (n := c + 1)
  refine le_antisymm ?_ ?_
  · rw [← Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le, eq_bot_iff]
    intro g hg
    exact Subgroup.mem_bot.mpr
      (eq_one_of_mem_filt _ le_rfl (lowerCentralSeries_le_filt _ (c + 1) hg))
  · by_contra h
    exact lowerCentralSeries_ne_bot _ frobenius_solvable c
      (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (by omega))

/-- The commutator subgroup is the subgroup of elements `g` with `g - 1` vanishing on the first
superdiagonal. -/
example (n : ℕ) (hn : 1 ≤ n) :
    commutator (caminaGroup (frobenius (AlgebraicClosure (ZMod 2)) 2) n) = filt _ 2 :=
  le_antisymm (commutator_le_filt_two _) (filt_two_le_commutator _ frobenius_solvable hn)

/-- The Camina property: outside the commutator subgroup, conjugacy classes are cosets of it. -/
example (n : ℕ) (hn : 1 ≤ n)
    (x : caminaGroup (frobenius (AlgebraicClosure (ZMod 2)) 2) n) (hx : x ∉ commutator _)
    (z : caminaGroup (frobenius (AlgebraicClosure (ZMod 2)) 2) n) (hz : z ∈ commutator _) :
    ∃ g, x * z = g * x * g⁻¹ :=
  (camina _ frobenius_solvable hn x hx (x * z)).mp ⟨z, hz, rfl⟩

/-- The commutator of two elements with level-`1` coefficients `a` and `b` has level-`2`
coefficient `a * b ^ 2 - b * a ^ 2`. -/
example (n : ℕ) (hn : 2 < n + 1) (g h : caminaGroup (frobenius (AlgebraicClosure (ZMod 2)) 2) n) :
    lead _ 2 ⁅g, h⁆ = lead _ 1 g * lead _ 1 h ^ 2 - lead _ 1 h * lead _ 1 g ^ 2 :=
  (commutator_mem_filt _ (filt_one _ g) (filt_one _ h)).2 hn

/-- Edge case: with `1 × 1` matrices the group is trivial, whatever the field and `σ`. -/
example (K : Type) [Field K] (σ : K →+* K) (g : caminaGroup σ 0) : g = 1 :=
  eq_one_of_mem_filt σ le_rfl (filt_one σ g)

end MathlibExtTest.GroupTheory.NilpotentCaminaClassUnboundedKourovka17Problem47
