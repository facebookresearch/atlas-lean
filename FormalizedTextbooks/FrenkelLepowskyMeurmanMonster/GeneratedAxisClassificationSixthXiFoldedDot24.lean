/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFoldedParity

/-! A bounded original row has no contributions outside its twenty-four genuine coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Folded intersection parity equals the exact dot product of a genuine twenty-four-bit row. -/
theorem generatedSixth_xi_folded_dot24 (n m : ℕ) (hm : m < 2 ^ 24) :
    generatedSixthXiFoldedParity (n &&& m) =
      ∑ j : Fin 24, generatedSixthXiBitScalar n j.val *
        generatedSixthXiBitScalar m j.val := by
  rw [generatedSixth_xi_folded_dot]
  change (∑ j : Fin (24 + 8), generatedSixthXiBitScalar n j.val *
    generatedSixthXiBitScalar m j.val) = _
  rw [Fin.sum_univ_add]
  have hz : (∑ j : Fin 8, generatedSixthXiBitScalar n (24 + j.val) *
      generatedSixthXiBitScalar m (24 + j.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hb : m.testBit (24 + j.val) = false := by
      apply Nat.testBit_eq_false_of_lt
      exact hm.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp only [generatedSixthXiBitScalar, hb, Bool.false_eq_true, ite_false, mul_zero]
  simp only [Fin.val_castAdd, Fin.val_natAdd, hz, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
