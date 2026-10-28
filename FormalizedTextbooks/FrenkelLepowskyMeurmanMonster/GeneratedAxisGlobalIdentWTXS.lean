/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWTX

/-! # Factory: normalized tensors with the power of two moved into the denominator (gident2)

The net field values of word-image tensors are multiples of a large power of two `2 ^ m`; the
factory stores them divided by `2 ^ m` (`tensorN k w m P N`).  Moving the factor `2 ^ m` into the
denominator gives the same rational tensor with tiny field values (`tensorN_shift`), so the
pairing criterion holds at field width `64` whatever the number of Xi letters of the words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false

/-- The factor `2 ^ m` of a normalized tensor moves into the denominator. -/
theorem tensorN_shift {k w m : ℕ} (hkw : k + m ≤ w) {P N : List ℕ} (hs : tensorNSize k P N = true)
    (D : ℚ) : tensorRat w (tensorN k w m P N) D = tensorRat w (tensorN k w 0 P N) (D / 2 ^ m) := by
  simp only [tensorNSize, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hs
  funext q i
  simp only [tensorRat]
  rw [tensorN, tcol_range_map _ 24 i.val i.isLt, tensorN, tcol_range_map _ 24 i.val i.isLt,
    (respaceS_col hkw (hs i.val i.isLt).1 (hs i.val i.isLt).2).2 q.val
      (lt_of_lt_of_le q.isLt (by norm_num)),
    (respaceS_col (by omega) (hs i.val i.isLt).1 (hs i.val i.isLt).2).2 q.val
      (lt_of_lt_of_le q.isLt (by norm_num))]
  push_cast
  rw [mul_one, div_div_eq_mul_div]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
