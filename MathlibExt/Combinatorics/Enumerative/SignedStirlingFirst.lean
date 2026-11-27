/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- **Signed Stirling numbers of the first kind.** For natural numbers $n$ and $k$, the signed
Stirling number of the first kind is the integer $(-1)^{n-k} c(n,k)$, where $c(n,k)$ is the
unsigned Stirling number of the first kind (the number of permutations of $n$ elements with
exactly $k$ cycles) and $n - k$ is truncated subtraction, equal to $0$ when $k > n$. -/
def signedStirlingFirst : ℕ → ℕ → ℤ :=
  fun n k => (-1 : ℤ) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)

theorem signedStirlingFirst_apply (n k : ℕ) :
    signedStirlingFirst n k = (-1 : ℤ) ^ (n - k) * (Nat.stirlingFirst n k : ℤ) :=
  rfl

theorem signedStirlingFirst_succ_succ (n k : ℕ) :
    signedStirlingFirst (n + 1) (k + 1) =
      signedStirlingFirst n k - (n : ℤ) * signedStirlingFirst n (k + 1) := by
  have h1 : n + 1 - (k + 1) = n - k := by omega
  have e1 : signedStirlingFirst (n + 1) (k + 1)
      = (-1 : ℤ) ^ (n + 1 - (k + 1)) * ((Nat.stirlingFirst (n + 1) (k + 1) : ℕ) : ℤ) := rfl
  have e2 : signedStirlingFirst n k
      = (-1 : ℤ) ^ (n - k) * ((Nat.stirlingFirst n k : ℕ) : ℤ) := rfl
  have e3 : signedStirlingFirst n (k + 1)
      = (-1 : ℤ) ^ (n - (k + 1)) * ((Nat.stirlingFirst n (k + 1) : ℕ) : ℤ) := rfl
  rw [e1, e2, e3, h1, Nat.stirlingFirst_succ_succ]
  push_cast
  by_cases h : k + 1 ≤ n
  · have h2 : n - k = (n - (k + 1)) + 1 := by omega
    rw [h2, pow_succ]
    ring
  · have hlt : n < k + 1 := by omega
    rw [Nat.stirlingFirst_eq_zero_of_lt hlt]
    push_cast
    ring

@[simp]
theorem signedStirlingFirst_succ_zero (n : ℕ) : signedStirlingFirst (n + 1) 0 = 0 := by
  have e : signedStirlingFirst (n + 1) 0
      = (-1 : ℤ) ^ (n + 1 - 0) * ((Nat.stirlingFirst (n + 1) 0 : ℕ) : ℤ) := rfl
  have h0 : Nat.stirlingFirst (n + 1) 0 = 0 := Nat.stirlingFirst_succ_zero n
  rw [e, h0]
  simp

@[simp]
theorem signedStirlingFirst_self (n : ℕ) : signedStirlingFirst n n = 1 := by
  have e : signedStirlingFirst n n
      = (-1 : ℤ) ^ (n - n) * ((Nat.stirlingFirst n n : ℕ) : ℤ) := rfl
  rw [e, Nat.sub_self, Nat.stirlingFirst_self]
  simp

theorem signedStirlingFirst_eq_zero_of_lt {n k : ℕ} (h : n < k) : signedStirlingFirst n k = 0 := by
  have e : signedStirlingFirst n k
      = (-1 : ℤ) ^ (n - k) * ((Nat.stirlingFirst n k : ℕ) : ℤ) := rfl
  rw [e, Nat.stirlingFirst_eq_zero_of_lt h]
  simp

end MetaMathlibExt
