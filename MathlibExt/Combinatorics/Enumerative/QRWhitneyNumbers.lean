/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# (q, r)-Whitney numbers of the first and second kind

Formalizes the q-integer as a finite geometric sum and the two triangular
recurrence arrays from the source. Concept `jis_sem_1510537ed21edced61e4c308`.
Source statement IDs: `jis_b6c9b8526668212b3d271ce0`, `jis_bfbfab3b67f1c02f167938f1`,
`jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`, `jis_dd5f8c454fc5760fb197859b`.
Original definitions via q-boson operators (`qw1`, `qw2`) are represented here by
the proved triangular recurrences (`identity4`, `identity5`) as the executable
definitions. The first-kind recurrence divides by `q ^ n`, so its API explicitly
assumes `q ≠ 0`; this avoids Lean's totalized inverse assigning unintended values
at the singular parameter `q = 0`.
-/

namespace MetaMathlibExt

@[expose] public section

namespace QRWhitney

/-- q-integer `[n]_q` as the finite geometric sum `∑ i in range n, q ^ i`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. Avoids any singularity at `q = 1`. -/
def qBrack (q : ℂ) (n : ℕ) : ℂ :=
  Finset.sum (Finset.range n) (fun i => q ^ i)

/-- (q, r)-Whitney numbers of the first kind `w_{m,r,q}(n, k)`, defined by the
triangular recurrence `identity4` split at `k = 0` vs `k + 1`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
noncomputable def whitneyFirst (m r q : ℂ) [NeZero q] : ℕ → ℕ → ℂ
  | 0 => fun | 0 => 1 | _ + 1 => 0
  | n + 1 => fun
    | 0 => (q ^ n)⁻¹ * (0 - (m * qBrack q n + r) * whitneyFirst m r q n 0)
    | k + 1 =>
      (q ^ n)⁻¹ *
        (whitneyFirst m r q n k -
          (m * qBrack q n + r) * whitneyFirst m r q n (k + 1))

/-- (q, r)-Whitney numbers of the second kind `W_{m,r,q}(n, k)`, defined by the
triangular recurrence `identity5` split at `k = 0` vs `k + 1`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
def whitneySecond (m r q : ℂ) : ℕ → ℕ → ℂ
  | 0 => fun | 0 => 1 | _ + 1 => 0
  | n + 1 => fun
    | 0 => r * whitneySecond m r q n 0
    | k + 1 =>
      q ^ k * whitneySecond m r q n k +
        (m * qBrack q (k + 1) + r) * whitneySecond m r q n (k + 1)

/-- Initial condition `w(0, 0) = 1`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneyFirst_zero_zero (m r q : ℂ) [NeZero q] : whitneyFirst m r q 0 0 = 1 :=
  rfl

/-- Initial condition `w(0, k + 1) = 0`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneyFirst_zero_succ (m r q : ℂ) [NeZero q] (k : ℕ) :
    whitneyFirst m r q 0 (k + 1) = 0 :=
  rfl

/-- First-kind recurrence at `k = 0`, i.e. `identity4` with `w(n, -1) = 0`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneyFirst_succ_zero (m r q : ℂ) [NeZero q] (n : ℕ) :
    whitneyFirst m r q (n + 1) 0 =
      (q ^ n)⁻¹ * (0 - (m * qBrack q n + r) * whitneyFirst m r q n 0) :=
  rfl

/-- First-kind recurrence `identity4` at `k + 1`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneyFirst_succ_succ (m r q : ℂ) [NeZero q] (n k : ℕ) :
    whitneyFirst m r q (n + 1) (k + 1) =
      (q ^ n)⁻¹ *
        (whitneyFirst m r q n k -
          (m * qBrack q n + r) * whitneyFirst m r q n (k + 1)) :=
  rfl

/-- Initial condition `W(0, 0) = 1`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneySecond_zero_zero (m r q : ℂ) : whitneySecond m r q 0 0 = 1 :=
  rfl

/-- Initial condition `W(0, k + 1) = 0`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneySecond_zero_succ (m r q : ℂ) (k : ℕ) :
    whitneySecond m r q 0 (k + 1) = 0 :=
  rfl

/-- Second-kind recurrence at `k = 0`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneySecond_succ_zero (m r q : ℂ) (n : ℕ) :
    whitneySecond m r q (n + 1) 0 = r * whitneySecond m r q n 0 :=
  rfl

/-- Second-kind recurrence `identity5` at `k + 1`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneySecond_succ_succ (m r q : ℂ) (n k : ℕ) :
    whitneySecond m r q (n + 1) (k + 1) =
      q ^ k * whitneySecond m r q n k +
        (m * qBrack q (k + 1) + r) * whitneySecond m r q n (k + 1) :=
  rfl

/-- First-kind support: `w(n, k) = 0` when `k > n`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneyFirst_eq_zero_of_lt {m r q : ℂ} [NeZero q] {n k : ℕ} (h : n < k) :
    whitneyFirst m r q n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact absurd h (by omega)
    | succ k => exact whitneyFirst_zero_succ m r q k
  | succ n ih =>
    cases k with
    | zero => exact absurd h (by omega)
    | succ k =>
      have h1 : n < k := Nat.lt_of_succ_lt_succ h
      have h2 : n < k + 1 := Nat.lt_trans h1 (Nat.lt_succ_self k)
      rw [whitneyFirst_succ_succ, ih h1, ih h2, mul_zero, sub_zero, mul_zero]

/-- Second-kind support: `W(n, k) = 0` when `k > n`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneySecond_eq_zero_of_lt {m r q : ℂ} {n k : ℕ} (h : n < k) :
    whitneySecond m r q n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact absurd h (by omega)
    | succ k => exact whitneySecond_zero_succ m r q k
  | succ n ih =>
    cases k with
    | zero => exact absurd h (by omega)
    | succ k =>
      have h1 : n < k := Nat.lt_of_succ_lt_succ h
      have h2 : n < k + 1 := Nat.lt_trans h1 (Nat.lt_succ_self k)
      rw [whitneySecond_succ_succ, ih h1, ih h2, mul_zero, mul_zero, add_zero]

/-- First-kind recurrence in the source one-based `k - 1` convention.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneyFirst_succ_eq (m r q : ℂ) [NeZero q] (n k : ℕ) (hk : 1 ≤ k) :
    whitneyFirst m r q (n + 1) k =
      (q ^ n)⁻¹ *
        (whitneyFirst m r q n (k - 1) -
          (m * qBrack q n + r) * whitneyFirst m r q n k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h : j + 1 - 1 = j := Nat.add_sub_cancel j 1
  rw [h]
  exact whitneyFirst_succ_succ m r q n j

/-- Second-kind recurrence in the source one-based `k - 1` convention.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
theorem whitneySecond_succ_eq (m r q : ℂ) (n k : ℕ) (hk : 1 ≤ k) :
    whitneySecond m r q (n + 1) k =
      q ^ (k - 1) * whitneySecond m r q n (k - 1) +
        (m * qBrack q k + r) * whitneySecond m r q n k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h : j + 1 - 1 = j := Nat.add_sub_cancel j 1
  rw [h]
  exact whitneySecond_succ_succ m r q n j

end QRWhitney

end

end MetaMathlibExt
