/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Log

/-!
# Gaps between powers of two

`MetaMathlibExt.two_pow_sub_succ_ne_two_pow` excludes powers of two obtained by
subtracting a sufficiently small positive number from a power of two.
-/

namespace MetaMathlibExt

/-- **A power of two minus a much smaller positive number is not a power of two.** Let $p$
and $k$ be natural numbers with $k \ge \lceil \log_2 (p + 1) \rceil + 2$. Then $2^k - (p + 1)$
is not a power of $2$: there is no natural number $m$ with $2^k - (p + 1) = 2^m$.

Under this hypothesis $2^k > p + 1$, so the subtraction is exact. The source assumes $p$ is
prime; the statement holds without that assumption.

Source: Steven J. Miller, Fei Peng, Tudor Popescu, Joshua M. Siktar, and Nawapan
Wattanawanichkul, *Walking to Infinity Along Some Number Theory Sequences*, INTEGERS 24 (2024),
Article A78, Lemma 2.5. -/
public theorem two_pow_sub_succ_ne_two_pow (p k : ℕ) (hk : Nat.clog 2 (p + 1) + 2 ≤ k) :
    ¬ ∃ m : ℕ, 2 ^ k - (p + 1) = 2 ^ m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hsmall : p + 1 < 2 ^ j :=
    (Nat.le_pow_clog Nat.one_lt_two (p + 1)).trans_lt (Nat.pow_lt_pow_right Nat.one_lt_two
      (by omega))
  rintro ⟨m, hm⟩
  have hlt : 2 ^ m < 2 ^ (j + 1) := by
    rw [← hm]
    exact Nat.sub_lt (Nat.two_pow_pos _) (Nat.succ_pos _)
  have hmj : m ≤ j := Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hlt)
  have hle := Nat.pow_le_pow_right (by decide : 0 < 2) hmj
  rw [Nat.pow_succ] at hm
  omega

end MetaMathlibExt
