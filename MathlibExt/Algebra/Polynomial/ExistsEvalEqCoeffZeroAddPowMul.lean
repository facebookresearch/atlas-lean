/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Polynomial_exists_eval_eq_coeff_zero_add_pow_mul.lean`
and
`P2M/Sol/S_Polynomial_exists_eval_eq_coeff_zero_add_pow_mul.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

namespace Polynomial

private theorem natCast_dvd_pow_self_of_forall_prime_dvd {N : ℤ} (hN : N ≠ 0) {d : ℕ}
    (hd : d ≠ 0) (h : ∀ q : ℕ, q.Prime → q ∣ d → (q : ℤ) ∣ N) : (d : ℤ) ∣ N ^ d := by
  have hn : N.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hN
  rw [Int.natCast_dvd, Int.natAbs_pow,
    ← Nat.factorization_prime_le_iff_dvd hd (pow_ne_zero d hn)]
  intro q hq
  rcases eq_or_ne (d.factorization q) 0 with h0 | h0
  · simp [h0]
  · have hqn : q ∣ N.natAbs := Int.natCast_dvd.1 (h q hq (Nat.dvd_of_factorization_pos h0))
    exact (Nat.factorization_lt q hd).le.trans
      ((hq.pow_dvd_iff_le_factorization (pow_ne_zero d hn)).1 (pow_dvd_pow_of_dvd hqn d))

/-- For a rational polynomial whose coefficient denominators are supported
on the primes dividing a nonzero integer `N`, the values `p (N ^ K * m)`
differ from the constant term `p.coeff 0` by a multiple of `N ^ (K - K₀)`,
for one uniform `K₀`, all `K ≥ K₀`, and all integers `m`. -/
public theorem exists_eval_eq_coeff_zero_add_pow_mul (p : Polynomial ℚ) (N : ℤ) (hN : N ≠ 0)
    (hden : ∀ k : ℕ, ∀ q : ℕ, q.Prime → q ∣ (p.coeff k).den → (q : ℤ) ∣ N) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ m : ℤ, ∃ z : ℤ,
      p.eval ((N : ℚ) ^ K * m) = p.coeff 0 + (N : ℚ) ^ (K - K₀) * z := by
  suffices h : ∃ K₀ : ℕ, ∀ k : ℕ, ∃ c : ℤ, (c : ℚ) = p.coeff k * (N : ℚ) ^ K₀ by
    obtain ⟨K₀, key⟩ := h
    choose c hc using key
    refine ⟨K₀, fun K hK m => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK
    refine ⟨∑ i ∈ Finset.range p.natDegree, c (i + 1) * N ^ ((K₀ + j) * i) * m ^ (i + 1), ?_⟩
    rw [Nat.add_sub_cancel_left, Polynomial.eval_eq_sum_range, Finset.sum_range_succ', pow_zero,
      mul_one]
    push_cast
    rw [add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc]
    ring
  refine ⟨∑ k ∈ p.support, (p.coeff k).den, fun k => ?_⟩
  by_cases hk : k ∈ p.support
  · have hle : (p.coeff k).den ≤ ∑ k ∈ p.support, (p.coeff k).den :=
      Finset.single_le_sum (f := fun k => (p.coeff k).den) (fun i _ => Nat.zero_le _) hk
    obtain ⟨t, ht⟩ : ((p.coeff k).den : ℤ) ∣ N ^ ∑ k ∈ p.support, (p.coeff k).den :=
      (natCast_dvd_pow_self_of_forall_prime_dvd hN (p.coeff k).den_nz (hden k)).trans
        (pow_dvd_pow N hle)
    refine ⟨(p.coeff k).num * t, ?_⟩
    have ht' : (N : ℚ) ^ (∑ k ∈ p.support, (p.coeff k).den) = ((p.coeff k).den : ℚ) * (t : ℚ) :=
      mod_cast ht
    rw [ht', ← mul_assoc, Rat.mul_den_eq_num, Int.cast_mul]
  · exact ⟨0, by simp [Polynomial.notMem_support_iff.mp hk]⟩

end Polynomial
