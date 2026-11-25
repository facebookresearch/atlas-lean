/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The block-length power of ten modulo a Mersenne prime

Let `M = 2 ^ p - 1` be prime and let `L = orderOf (10 : ZMod M)` be the period of the decimal
expansion of `1 / M`. When `p ∣ L`, the repeating block of `1 / M` splits into `p` blocks of
`L / p` digits each, and `10 ^ (L / p)` is congruent modulo `M` to `2 ^ r` for some
`1 ≤ r ≤ p - 1`. The statement and its docstring, with the source citation, are unchanged from the
wanted entry in `WantedExt.NumberTheory.Digits.MersenneReciprocalBlocksWanted` that this module
replaces.

The proof works in the field `ZMod M`. There `2` is a primitive `p`-th root of unity, because
`2 ^ p = M + 1` while `1 < 2 ^ l < M` for `0 < l < p`. The `p`-th power of `10 ^ (L / p)` is
`10 ^ L = 1`, so `10 ^ (L / p) = 2 ^ r` for some `r < p` (`IsPrimitiveRoot.eq_pow_of_pow_eq_one`).
Finally `r ≠ 0`: since `M` does not divide `10`, the order `L` is positive, so `0 < L / p < L`.

## Main results

* `MetaMathlibExt.ten_pow_blockLength_modEq_two_pow`: if `2 ^ p - 1` is prime and `p` divides
  `L = orderOf (10 : ZMod (2 ^ p - 1))`, then `10 ^ (L / p) ≡ 2 ^ r [MOD 2 ^ p - 1]` for some
  `r ∈ Finset.Icc 1 (p - 1)`.
-/

namespace MetaMathlibExt

/-- **The block-length power of ten is a power of two modulo the Mersenne prime.** Let $p$ be a
natural number such that $M = 2^p - 1$ is prime, let $L$ be the multiplicative order of $10$ modulo
$M$ (the period of the decimal expansion of $1/M$), and suppose that $p$ divides $L$. Then there is
a natural number $r$ with $1 \le r \le p - 1$ such that $10^{L/p} \equiv 2^r \pmod{M}$.

Source: Amitabha Tripathi, *A Note on the Decimal Expansion of Reciprocals of Mersenne Primes*,
INTEGERS 24 (2024), Article A14, Proposition 1 (`integers-2024-A14-prop-1`). -/
public theorem ten_pow_blockLength_modEq_two_pow (p : ℕ) (hM : (2 ^ p - 1).Prime)
    (hdvd : p ∣ orderOf (10 : ZMod (2 ^ p - 1))) :
    ∃ r ∈ Finset.Icc 1 (p - 1),
      10 ^ (orderOf (10 : ZMod (2 ^ p - 1)) / p) ≡ 2 ^ r [MOD 2 ^ p - 1] := by
  have : Fact (2 ^ p - 1).Prime := ⟨hM⟩
  -- `2 ^ p - 1` is prime only for `p ≥ 2`.
  have hp2 : 2 ≤ p := by
    by_contra h
    interval_cases p
    · exact Nat.not_prime_zero hM
    · exact Nat.not_prime_one hM
  -- `2 ^ p - 1` does not divide `10`, so `10` is nonzero modulo it and has positive order.
  have hndvd : ¬ 2 ^ p - 1 ∣ 10 := by
    intro h
    have hle : 2 ^ p - 1 ≤ 10 := Nat.le_of_dvd (by norm_num) h
    have hp3 : p ≤ 3 := by
      by_contra hp
      have : 2 ^ 4 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases p <;> norm_num at h
  have h10 : (10 : ZMod (2 ^ p - 1)) ≠ 0 := by
    intro h
    apply hndvd
    rw [← ZMod.natCast_eq_zero_iff]
    exact_mod_cast h
  have hLpos : 0 < orderOf (10 : ZMod (2 ^ p - 1)) := by
    refine orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2 ^ p - 1 - 1, ?_, ?_⟩)
    · have : 2 ^ 2 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp2
      omega
    · exact ZMod.pow_card_sub_one_eq_one h10
  -- `2` is a primitive `p`-th root of unity modulo `2 ^ p - 1`.
  have h2 : IsPrimitiveRoot (2 : ZMod (2 ^ p - 1)) p := by
    refine IsPrimitiveRoot.mk_of_lt _ (by omega) ?_ ?_
    · have h := ZMod.natCast_self (2 ^ p - 1)
      rw [Nat.cast_sub Nat.one_le_two_pow, sub_eq_zero] at h
      exact_mod_cast h
    · -- For `0 < l < p` we have `1 < 2 ^ l < 2 ^ p - 1`, so `2 ^ l` is not `1` modulo `2 ^ p - 1`.
      intro l hl0 hlp h
      have h' : ((2 ^ l : ℕ) : ZMod (2 ^ p - 1)) = ((1 : ℕ) : ZMod (2 ^ p - 1)) := by
        exact_mod_cast h
      rw [ZMod.natCast_eq_natCast_iff'] at h'
      have hl : 2 ^ l ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hp1 : 2 ^ p = 2 * 2 ^ (p - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have h1p : 1 < 2 ^ (p - 1) := Nat.one_lt_two_pow (by omega)
      have h1l : 1 < 2 ^ l := Nat.one_lt_two_pow (by omega)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
      omega
  -- `10 ^ (L / p)` is a `p`-th root of unity, hence a power `2 ^ r` with `r < p`.
  have : NeZero p := ⟨by omega⟩
  have hξ : ((10 : ZMod (2 ^ p - 1)) ^ (orderOf (10 : ZMod (2 ^ p - 1)) / p)) ^ p = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hdvd, pow_orderOf_eq_one]
  obtain ⟨r, hrp, hr⟩ := h2.eq_pow_of_pow_eq_one hξ
  -- The exponent `r` is not `0`, since `0 < L / p < L`.
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hr
    have hdiv := orderOf_dvd_of_pow_eq_one hr.symm
    have hpos : 0 < orderOf (10 : ZMod (2 ^ p - 1)) / p :=
      Nat.div_pos (Nat.le_of_dvd hLpos hdvd) (by omega)
    have hlt : orderOf (10 : ZMod (2 ^ p - 1)) / p < orderOf (10 : ZMod (2 ^ p - 1)) :=
      Nat.div_lt_self hLpos (by omega)
    exact absurd (Nat.le_of_dvd hpos hdiv) (by omega)
  refine ⟨r, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact hr.symm

end MetaMathlibExt
