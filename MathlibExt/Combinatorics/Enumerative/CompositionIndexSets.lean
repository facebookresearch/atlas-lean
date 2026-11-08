/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

namespace MetaMathlibExt

@[expose] public section

/-- The index set `S(m, n, q)`: the naturals `k` with
`2k ≡ n - q (mod m)` and `k ≤ ⌊(n - 1) / 2⌋`. The bound is written
`2 * k < n`, which is equivalent for naturals (and empty at `n = 0`).

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 13 (`jis-2024-24.3.6-thm-13`). -/
public def compositionHalfIndexSet (m n q : ℕ) : Set ℕ :=
  {k | 2 * (k : ℤ) ≡ (n : ℤ) - (q : ℤ) [ZMOD (m : ℤ)] ∧ 2 * k < n}

/-- Membership in `S(m, n, q)` unfolded.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 13 (`jis-2024-24.3.6-thm-13`). -/
public theorem mem_compositionHalfIndexSet {m n q k : ℕ} :
    k ∈ compositionHalfIndexSet m n q ↔
      2 * (k : ℤ) ≡ (n : ℤ) - (q : ℤ) [ZMOD (m : ℤ)] ∧ 2 * k < n :=
  Iff.rfl

/-- Boundary characteristic: `S(m, 0, q)` is empty.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 13 (`jis-2024-24.3.6-thm-13`). -/
public theorem compositionHalfIndexSet_zero (m q : ℕ) :
    compositionHalfIndexSet m 0 q = ∅ := by
  ext k
  simp only [mem_compositionHalfIndexSet, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, h⟩
  omega

/-- The index set `T(m, n, q)`: the naturals `k` with
`k ≡ n - q (mod m)` and `0 ≤ k ≤ n - 1`. The bound is written
`k < n`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 17 (`jis-2024-24.3.6-thm-17`). -/
public def compositionIndexSet (m n q : ℕ) : Set ℕ :=
  {k | (k : ℤ) ≡ (n : ℤ) - (q : ℤ) [ZMOD (m : ℤ)] ∧ k < n}

/-- Membership in `T(m, n, q)` unfolded.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 17 (`jis-2024-24.3.6-thm-17`). -/
public theorem mem_compositionIndexSet {m n q k : ℕ} :
    k ∈ compositionIndexSet m n q ↔
      (k : ℤ) ≡ (n : ℤ) - (q : ℤ) [ZMOD (m : ℤ)] ∧ k < n :=
  Iff.rfl

/-- Boundary characteristic: `T(m, 0, q)` is empty.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Theorem 17 (`jis-2024-24.3.6-thm-17`). -/
public theorem compositionIndexSet_zero (m q : ℕ) :
    compositionIndexSet m 0 q = ∅ := by
  ext k
  simp only [mem_compositionIndexSet, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, h⟩
  omega

/-- The doubling identity `S(2m, 2n, 2q) = T(m, n, q)`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Lemma 18 (`jis-2024-24.3.6-lem-18`). -/
public theorem compositionHalfIndexSet_double (m n q : ℕ) :
    compositionHalfIndexSet (2 * m) (2 * n) (2 * q)
      = compositionIndexSet m n q := by
  have key : ∀ a b : ℤ, (2 * a ≡ 2 * b [ZMOD 2 * (m : ℤ)])
      ↔ a ≡ b [ZMOD (m : ℤ)] := by
    intro a b
    rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd]
    have hsub : 2 * b - 2 * a = 2 * (b - a) := by ring
    rw [hsub]
    exact mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)
  ext k
  simp only [mem_compositionHalfIndexSet, mem_compositionIndexSet,
    Nat.cast_mul, Nat.cast_ofNat]
  have hrw : 2 * (n : ℤ) - 2 * (q : ℤ) = 2 * ((n : ℤ) - (q : ℤ)) := by ring
  rw [hrw]
  constructor
  · rintro ⟨h, hk⟩
    exact ⟨(key (k : ℤ) ((n : ℤ) - (q : ℤ))).mp h, by omega⟩
  · rintro ⟨h, hk⟩
    exact ⟨(key (k : ℤ) ((n : ℤ) - (q : ℤ))).mpr h, by omega⟩

end

end MetaMathlibExt
