/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphism

/-! Concrete stabilizer completeness prerequisites for the Golay automorphism group.
No Mathieu group order is assumed. The minimum code weight rules out a
nontrivial code automorphism moving only two coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- A Golay codeword supported in coordinates 6 and 7 is zero. -/
theorem golayCode_eq_zero_of_support_two (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode)
    (hs : ∀ i : Fin 24, i ≠ 6 → i ≠ 7 → c i = 0) : c = 0 := by
  by_contra hn
  have hlo := golayCode_weight_ge_eight c hc hn
  have hbound : (∑ i : Fin 24, (c i).val) ≤
      ∑ i : Fin 24, (if i = 6 ∨ i = 7 then 1 else 0 : ℕ) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i = 6 ∨ i = 7
    · simp only [hi, ite_true]
      have h := ZMod.val_lt (c i)
      omega
    · have hci := hs i (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h))
      simp only [hi, ite_false, hci, ZMod.val_zero]
      exact Nat.le_refl 0
  have hsum : (∑ i : Fin 24, (if i = 6 ∨ i = 7 then 1 else 0 : ℕ)) = 2 := by decide
  rw [hsum] at hbound
  omega

/-- Two actual Golay words agreeing outside coordinates 6 and 7 are equal. -/
theorem golayCode_eq_of_agree_except_two (c d : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hd : d ∈ golayCode)
    (hcd : ∀ i : Fin 24, i ≠ 6 → i ≠ 7 → c i = d i) : c = d := by
  apply sub_eq_zero.mp
  apply golayCode_eq_zero_of_support_two (c - d) (golayCode.sub_mem hc hd)
  intro i hi hj
  change c i - d i = 0
  rw [hcd i hi hj, sub_self]

/-- The pointwise stabilizer of the other 22 coordinates is trivial in the actual group. -/
theorem golayAutomorphism_eq_one_of_fix_except_two (p : golayAutomorphismSubgroup)
    (hp : ∀ i : Fin 24, i ≠ 6 → i ≠ 7 → p.val i = i) : p = 1 := by
  apply golayAutomorphism_code_action_injective
  funext c
  change golayPermute p.val c.val = c.val
  apply golayCode_eq_of_agree_except_two _ _ ((p.property c.val).mp c.property) c.property
  intro i hi hj
  change c.val (p.val.symm i) = c.val i
  have h := hp i hi hj
  have hh := congrArg p.val.symm h
  rw [p.val.symm_apply_apply] at hh
  exact congrArg c.val hh.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
