/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Josephus survivor function.** For natural numbers $k$ and $n$, the Josephus function
$J_k(n)$ is defined by recursion on $n$: $J_k(0) = 0$ and
$J_k(n+1) = ((J_k(n) + k - 1) \bmod (n+1)) + 1$, where subtraction of natural numbers is
truncated at $0$.

For $k \ge 2$ and $n \ge 1$, $J_k(n)$ is the one-based position of the sole survivor when every
$k$-th person is eliminated from a circle of $n$ people; the value $J_k(0) = 0$ only anchors the
recursion.

Source: concept `jis_sem_e1c9a353312d2a1564410d6e`; source statements
`jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`,
`jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`,
`jis_fe4f24c64ecfdad23577e877`; clauses `domain`, `meaning`. -/
public def josephus (k : Nat) : Nat → Nat
  | 0 => 0
  | (n + 1) => ((josephus k n + k - 1) % (n + 1)) + 1

/-- **The Josephus function at one.** For every natural number $k \ge 2$, the Josephus function
$J_k$ for elimination step $k$ satisfies $J_k(1) = 1$.

Source: concept `jis_sem_e1c9a353312d2a1564410d6e`; source statements
`jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`,
`jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`,
`jis_fe4f24c64ecfdad23577e877`; clause `base`. The hypothesis `_hk` records the
source domain `k ≥ 2` and is unused by the proof. -/
public theorem josephus_one (k : Nat) (_hk : 2 ≤ k) : josephus k 1 = 1 := by
  simp only [josephus]
  omega

/-- **Euler recurrence for the Josephus function.** For all natural numbers $k \ge 2$ and
$n \ge 1$, the Josephus function $J_k$ for elimination step $k$ satisfies
$J_k(n+1) = ((J_k(n) + k - 1) \bmod (n+1)) + 1$.

Source: concept `jis_sem_e1c9a353312d2a1564410d6e`; source statements
`jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`,
`jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`,
`jis_fe4f24c64ecfdad23577e877`; clause `euler_recurrence`. The hypotheses `_hk` and `_hn`
record the source domain `k ≥ 2`, `n ≥ 1` and are unused by the proof. -/
public theorem josephus_succ (k n : Nat) (_hk : 2 ≤ k) (_hn : 1 ≤ n) :
    josephus k (n + 1) = ((josephus k n + k - 1) % (n + 1)) + 1 := by
  simp only [josephus]

/-- **Range of the Josephus function.** For all natural numbers $k \ge 2$ and $n \ge 1$, the
Josephus function $J_k$ for elimination step $k$ satisfies $1 \le J_k(n) \le n$.

Source: concept `jis_sem_e1c9a353312d2a1564410d6e`; source statements
`jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`,
`jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`,
`jis_fe4f24c64ecfdad23577e877`; clause `range`. The hypothesis `_hk` records the source domain
`k ≥ 2` and is unused by the proof. -/
public theorem josephus_range (k n : Nat) (_hk : 2 ≤ k) (hn : 1 ≤ n) :
    1 ≤ josephus k n ∧ josephus k n ≤ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : josephus k (m + 1) = ((josephus k m + k - 1) % (m + 1)) + 1 := by
    simp only [josephus]
  rw [h]
  constructor
  · omega
  · have hpos : 0 < m + 1 := by omega
    have hmod : (josephus k m + k - 1) % (m + 1) < m + 1 :=
      Nat.mod_lt _ hpos
    omega

end

end MetaMathlibExt
