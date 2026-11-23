/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.Rabin
import Mathlib.Tactic.NormNum.Prime

/-!
# Rabin function tests

Concrete values of the Rabin function and of the `p ≡ 3 (mod 4)` square root, and a
non-vacuity check of the factoring theorem: a square-root oracle exists (chosen classically),
and for `n = 3 · 5` the theorem gives exactly `4` of the `φ(15) = 8` units.
-/

set_option autoImplicit false

namespace Cslib.Crypto.PublicKey.Rabin

private instance fact_prime_three' : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance fact_prime_five' : Fact (Nat.Prime 5) := ⟨by norm_num⟩

example : rabinFunction 15 4 2 = 12 := by decide

example (x : ZMod 15) : rabinFunction 15 (2 * 3) x = (x + 3) ^ 2 - 9 := by
  rw [rabinFunction_two_mul]
  norm_num

/-- `2 = 3²` in `ZMod 7` and `7 ≡ 3 (mod 4)`, so `2^2 = 4` is a square root of `2`. -/
example : ((2 : ZMod 7) ^ ((7 + 1) / 4)) ^ 2 = 2 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact pow_add_one_div_four_sq (by norm_num) ⟨3, rfl⟩

example : (2 : ZMod 7) ^ ((7 + 1) / 4) = 4 := by decide

example : Nat.gcd 6 (3 * 5) ∈ ({3, 5} : Finset ℕ) := by decide

example : (Nat.gcd 6 (3 * 5) ∈ ({3, 5} : Finset ℕ)) ↔ (3 ∣ 6 ∧ ¬ 5 ∣ 6) ∨ (5 ∣ 6 ∧ ¬ 3 ∣ 6) :=
  gcd_mul_mem_iff (by norm_num) (by norm_num) (by norm_num) 6

example : Cslib.Crypto.PublicKey.Assumptions.IsFactorization (3 * 5) (3, 3 * 5 / 3) :=
  isFactorization_of_gcd_mem (by norm_num) (by norm_num) (by simp)

open Classical in
/-- A square-root oracle: some square root of `x` when one exists, `0` otherwise. -/
noncomputable def someRoot {n : ℕ} (x : ZMod n) : ZMod n :=
  if h : ∃ y : ZMod n, y ^ 2 = x then h.choose else 0

theorem someRoot_sq {n : ℕ} (k : ZMod n) : someRoot (k ^ 2) ^ 2 = k ^ 2 := by
  have h : ∃ y : ZMod n, y ^ 2 = k ^ 2 := ⟨k, rfl⟩
  unfold someRoot
  split_ifs
  exact h.choose_spec

/-- The factoring theorem is not vacuous: for `n = 15` and the oracle `someRoot`, exactly half of
the `φ(15) = 8` units give a factor. -/
example : 2 * (Finset.univ.filter fun k : (ZMod (3 * 5))ˣ =>
    Nat.gcd ((k : ZMod (3 * 5)) - someRoot ((k : ZMod (3 * 5)) ^ 2)).val (3 * 5) ∈
      ({3, 5} : Finset ℕ)).card = 8 := by
  rw [two_mul_card_gcd_mem_eq_totient (by norm_num) (by norm_num) someRoot
    (fun k => someRoot_sq _)]
  decide

/-- The partial-oracle count is not vacuous: an oracle answering only on `Q = {1}` with the root
`1` succeeds on exactly the two square roots `4` and `11` of `1` modulo `15` other than `±1`. -/
example : 2 * (Finset.univ.filter fun k : (ZMod (3 * 5))ˣ => (k : ZMod (3 * 5)) ^ 2 ∈
    ({1} : Set (ZMod (3 * 5))) ∧
      Nat.gcd ((k : ZMod (3 * 5)) - (fun _ => 1) ((k : ZMod (3 * 5)) ^ 2)).val (3 * 5) ∈
        ({3, 5} : Finset ℕ)).card = 4 := by
  rw [two_mul_card_gcd_mem_eq_card (by norm_num) (by norm_num) _ (fun _ => 1)
    (fun k hk => by simp only [Set.mem_singleton_iff] at hk; rw [hk, one_pow])]
  decide

end Cslib.Crypto.PublicKey.Rabin
