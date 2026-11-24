/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import MathlibExt.NumberTheory.Digits.KaprekarProjectiveDoubling

/-!
# A totient bound for the projective order of 2

For an odd base `B > 3`, the projective order of `2` is at most half of `B.totient`,
the index of the subgroup `{1, -1}` in the unit group modulo `B`.
-/

namespace MetaMathlibExt

/-- **Projective order of 2 is at most half the totient.** For every odd natural number $B > 3$,
the projective order of $2$ modulo $B$ satisfies $\lambda(B) \le \lfloor \varphi(B)/2 \rfloor$,
where $\varphi$ is Euler's totient function.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7, Lemma 21
(quoting Kay and Downes-Ward, Theorem 2) (`jis-2026-26.4.7-lem-21`). -/
public theorem projectiveOrderTwo_le_totient_div_two (B : ℕ) (hB : Odd B)
    (hB3 : 3 < B) :
    projectiveOrderTwo B ≤ B.totient / 2 := by
  have : NeZero B := ⟨by omega⟩
  have : Fact (1 < B) := ⟨by omega⟩
  let H := Subgroup.zpowers (-1 : (ZMod B)ˣ)
  let u := ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hB)
  have hcard : Nat.card H = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_zpowers]
    simp [ZMod.ringChar_zmod_n, show B ≠ 2 by omega]
  have hindex : H.index = B.totient / 2 := by
    rw [H.index_eq_card_div, hcard, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [← hindex]
  apply Nat.sInf_le
  refine ⟨H.index_pos, ?_⟩
  obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.mpr (H.pow_index_mem u)
  have hpow : (-1 : ZMod B) ^ k = 2 ^ H.index := by
    simpa [u, ZMod.coe_unitOfCoprime] using congrArg Units.val hk
  rw [← hpow]
  exact neg_one_pow_eq_or _ _

end MetaMathlibExt
