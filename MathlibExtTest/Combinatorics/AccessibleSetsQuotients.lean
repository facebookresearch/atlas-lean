/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.AccessibleSetsQuotients

namespace MetaMathlibExt

-- With divisor one the quotient set is the original set.
example (A : Set ℕ) (r : ℕ) (hA : IsRAccessible r A) : IsRAccessible r A := by
  have h := accessible_integral_quotients A 1 r Nat.one_pos (by simpa only [Nat.mul_one] using hA)
  have hset : {n : ℕ | 0 < n ∧ ∃ a ∈ A, a = n * 1} = A := by
    ext n
    constructor
    · rintro ⟨_, a, ha, rfl⟩
      simpa only [Nat.mul_one] using ha
    · intro hn
      exact ⟨hA.1 hn, n, hn, (Nat.mul_one n).symm⟩
  rwa [hset] at h

-- Dividing the positive even gaps by two produces all positive gaps.
example : IsRAccessible 1 (Set.Ioi (0 : ℕ)) := by
  let A : Set ℕ := {n | 0 < n ∧ 2 ∣ n}
  have hA : IsRAccessible 2 A := by
    apply two_accessible_of_internal_diffsequences A (fun _ hn ↦ hn.1)
    intro k _
    let x (i : Fin k) : ℕ+ := ⟨2 * ((i : ℕ) + 1), by omega⟩
    refine ⟨x, fun i ↦ ⟨(x i).pos, ⟨(i : ℕ) + 1, rfl⟩⟩, ?_⟩
    intro i hi
    refine ⟨2, ⟨by decide, dvd_rfl⟩, ?_⟩
    change ((2 * (i + 1 + 1) : ℕ) : ℤ) - ((2 * (i + 1) : ℕ) : ℤ) = 2
    omega
  have h := accessible_integral_quotients A 2 1 (by decide) hA
  have hset : {n : ℕ | 0 < n ∧ ∃ a ∈ A, a = n * 2} = Set.Ioi (0 : ℕ) := by
    ext n
    exact ⟨fun hn ↦ hn.1, fun hn ↦
      ⟨hn, n * 2, ⟨Nat.mul_pos hn (by decide), dvd_mul_left 2 n⟩, rfl⟩⟩
  rwa [hset] at h

end MetaMathlibExt
