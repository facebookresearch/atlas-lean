/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.NumberTheory.Rayleigh
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence

/-!
# Fibonacci and Pell numeration identities from the Olympic games

Statements from Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three
Impartial Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3.

The paper's Fibonacci numbers `F_n` are `Nat.fib n`, its Pell numbers `P_n` are `pellNumber n`
(`0, 1, 2, 5, 12, …`), and its half-companion Pell numbers `H_n` are `pellLucasSequence n`
(`1, 1, 3, 7, 17, …`, OEIS A001333). The constant `α = 1 + √2` is fixed in Section 4 of the
paper.

The bronze numbers `B_n` (`0, 1, 3, 10, 33, …`, `B_{n+1} = 3B_n + B_{n-1}`) are
`lucasU bronzeLucasParams n`; the companion bronze numbers of the first and second type are
`C_n = B_{n+1} - 2B_n` (`1, 1, 4, 13, 43, …`) and `D_n = B_{n+1} - B_n` (`1, 2, 7, 23, 76, …`),
i.e. the paper's `C_n = B_n + B_{n-1}` and `D_n = 2B_n + B_{n-1}` with `B_{-1} = 1`.

The floor identities (Theorems 2, 6, 10) concern the representations of Theorems 1, 4, 5, 8, 9
built greedily in their proofs ("choose the largest …"). The greedy digit sequence is
characterized by partial sums: for every `m`, the part of the sum below the `m`-th term is less
than the `m`-th term. The printed digit conditions do not single it out, and the identities fail
for other digit sequences satisfying them (e.g. `26 = F_7 + 2F_5 + F_3 + F_1` satisfies the
conditions of Theorem 1 with nonzero top digit, but `⌊26φ⌋ = 42 ≠ 41 = F_8 + 2F_6 + F_4 + F_2`).
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- For `k ≥ 0`, `F_{2k+1} φ = F_{2k+2} + ((√5 - 1) / 2)^{2k+1}` and
`F_{2k+1} (1 + φ) = F_{2k+3} + ((√5 - 1) / 2)^{2k+1}`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Proposition 1. -/
theorem_wanted fib_odd_mul_goldenRatio (k : ℕ) :
    (Nat.fib (2 * k + 1) : ℝ) * Real.goldenRatio =
        Nat.fib (2 * k + 2) + ((Real.sqrt 5 - 1) / 2) ^ (2 * k + 1) ∧
      (Nat.fib (2 * k + 1) : ℝ) * (1 + Real.goldenRatio) =
        Nat.fib (2 * k + 3) + ((Real.sqrt 5 - 1) / 2) ^ (2 * k + 1)

/-- Every positive integer `t` is `∑_{k=0}^{n} a_{2k+1} F_{2k+1}` (here `a k` is the paper's
`a_{2k+1}`) with `F_{2n+1} ≤ t < F_{2n+3}`, `a_1 ≤ 1`, `a_{2k+1} ≤ 2` for `k ≥ 1`, no
`2F_3 + F_1`, and no `2F_{2k+1} + 2F_{2k-1}`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 1. -/
theorem_wanted exists_odd_fib_representation {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), Nat.fib (2 * n + 1) ≤ t ∧ t < Nat.fib (2 * n + 3) ∧
      t = ∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 1) ∧
      a 0 ≤ 1 ∧ (∀ k, 1 ≤ k → a k ≤ 2) ∧ ¬ (a 1 = 2 ∧ a 0 = 1) ∧
      ∀ k, ¬ (a (k + 1) = 2 ∧ a k = 2)

/-- For `k ≥ 0` and `α = 1 + √2`: `P_{2k+1} α = P_{2k+2} + (√2 - 1)^{2k+1}` and
`H_{2k} α = H_{2k+1} + √2 (√2 - 1)^{2k}`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Proposition 2 (1), (2). -/
theorem_wanted pellNumber_odd_mul_one_add_sqrt_two (k : ℕ) :
    (pellNumber (2 * k + 1) : ℝ) * (1 + Real.sqrt 2) =
        pellNumber (2 * k + 2) + (Real.sqrt 2 - 1) ^ (2 * k + 1) ∧
      (pellLucasSequence (2 * k) : ℝ) * (1 + Real.sqrt 2) =
        pellLucasSequence (2 * k + 1) + Real.sqrt 2 * (Real.sqrt 2 - 1) ^ (2 * k)

/-- Let `R_k = 2P_k` for odd `k` and `R_k = H_k` for even `k`. Every positive integer `t` is
`∑_{k=0}^{n} a_k R_k` with `R_n ≤ t < R_{n+1}`, `a_0 ≤ 1`, `a_1 = 1 → a_0 = 0`, `a_{2k} ≤ 3`,
`a_{2k+1} ≤ 1`, `a_{2k} = 3 → a_{2k-1} = a_{2k+1} = 0` for `k ≥ 1`, and
`a_{2k} = 3 → a_{2k-2} < 3 ∧ a_{2k+2} < 3`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 4. -/
theorem_wanted exists_two_pell_halfCompanion_representation (R : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k)
    {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), R n ≤ t ∧ t < R (n + 1) ∧
      t = ∑ k ∈ range (n + 1), a k * R k ∧
      a 0 ≤ 1 ∧ (a 1 = 1 → a 0 = 0) ∧ (∀ k, a (2 * k) ≤ 3 ∧ a (2 * k + 1) ≤ 1) ∧
      (∀ k, 1 ≤ k → a (2 * k) = 3 → a (2 * k - 1) = 0 ∧ a (2 * k + 1) = 0) ∧
      (∀ k, 1 ≤ k → a (2 * k) = 3 → a (2 * k - 2) < 3) ∧
      (∀ k, a (2 * k) = 3 → a (2 * k + 2) < 3)

/-- Let `R_k = P_k` for odd `k` and `R_k = H_k` for even `k`. Every positive integer `t` is
`∑_{k=1}^{n} a_k R_k` with `R_n ≤ t < R_{n+1}`, `a_1 ≤ 2`, `a_1 = 2 → a_2 = 0`,
`a_{2k+1} ≤ 3`, `a_{2k} ≤ 1`, `a_{2k+1} = 3 → a_{2k} = a_{2k+2} = 0` for `k ≥ 1`, and
`a_{2k+1} = 3 → a_{2k-1} < 3 ∧ a_{2k+3} < 3`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 5. -/
theorem_wanted exists_pell_halfCompanion_representation (R : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then pellNumber k else pellLucasSequence k)
    {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), 1 ≤ n ∧ R n ≤ t ∧ t < R (n + 1) ∧
      t = ∑ k ∈ Icc 1 n, a k * R k ∧
      a 1 ≤ 2 ∧ (a 1 = 2 → a 2 = 0) ∧ (∀ k, a (2 * k + 1) ≤ 3 ∧ a (2 * k) ≤ 1) ∧
      (∀ k, 1 ≤ k → a (2 * k + 1) = 3 → a (2 * k) = 0 ∧ a (2 * k + 2) = 0) ∧
      (∀ k, 1 ≤ k → a (2 * k + 1) = 3 → a (2 * k - 1) < 3 ∧ a (2 * k + 3) < 3)

/-- The Lucas-sequence parameters `(P, Q) = (3, -1)`: `lucasU bronzeLucasParams n` is the `n`-th
bronze number `B_n`, with `B_0 = 0`, `B_1 = 1`, `B_{n+1} = 3B_n + B_{n-1}`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (bronze numbers). -/
def bronzeLucasParams : LucasSequenceParams where
  p := 3
  q := -1
  q_ne_zero := by decide

/-- The bronze numbers satisfy `B_{n+2} = 3B_{n+1} + B_n`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (bronze numbers). -/
theorem lucasU_bronzeLucasParams_add_two (n : ℕ) :
    lucasU bronzeLucasParams (n + 2) =
      3 * lucasU bronzeLucasParams (n + 1) + lucasU bronzeLucasParams n := by
  simp [lucasU, bronzeLucasParams]

/-- The first bronze numbers are `0, 1, 3, 10, 33, 109`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (bronze numbers). -/
theorem lucasU_bronzeLucasParams_values :
    (List.range 6).map (lucasU bronzeLucasParams) = [0, 1, 3, 10, 33, 109] := by
  decide

/-- The companion bronze numbers of the first type, `C_n = B_{n+1} - 2B_n = B_n + B_{n-1}`
(`C_0 = C_1 = 1`, `C_{n+1} = 3C_n + C_{n-1}`).

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (companion bronze
numbers of the first type). -/
def bronzeCompanionFirst (n : ℕ) : ℤ :=
  lucasU bronzeLucasParams (n + 1) - 2 * lucasU bronzeLucasParams n

/-- The companion bronze numbers of the second type, `D_n = B_{n+1} - B_n = 2B_n + B_{n-1}`
(`D_0 = 1`, `D_1 = 2`, `D_{n+1} = 3D_n + D_{n-1}`).

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (companion bronze
numbers of the second type). -/
def bronzeCompanionSecond (n : ℕ) : ℤ :=
  lucasU bronzeLucasParams (n + 1) - lucasU bronzeLucasParams n

/-- `C_{n+2} = 3C_{n+1} + C_n`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4. -/
theorem bronzeCompanionFirst_add_two (n : ℕ) :
    bronzeCompanionFirst (n + 2) = 3 * bronzeCompanionFirst (n + 1) + bronzeCompanionFirst n := by
  simp only [bronzeCompanionFirst, lucasU_bronzeLucasParams_add_two (n + 1),
    lucasU_bronzeLucasParams_add_two n]
  ring

/-- `D_{n+2} = 3D_{n+1} + D_n`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4. -/
theorem bronzeCompanionSecond_add_two (n : ℕ) :
    bronzeCompanionSecond (n + 2) = 3 * bronzeCompanionSecond (n + 1) + bronzeCompanionSecond n := by
  simp only [bronzeCompanionSecond, lucasU_bronzeLucasParams_add_two (n + 1),
    lucasU_bronzeLucasParams_add_two n]
  ring

/-- The first companion bronze numbers: `C = 1, 1, 4, 13, 43, …` and `D = 1, 2, 7, 23, 76, …`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4. -/
theorem bronzeCompanion_values :
    (List.range 5).map bronzeCompanionFirst = [1, 1, 4, 13, 43] ∧
      (List.range 5).map bronzeCompanionSecond = [1, 2, 7, 23, 76] := by
  decide

/-- One move of the heap game with octal code `0·d₁d₂d₃…`, where `d_i = 1` when `i` lies in the
Beatty sequence `{⌊kα⌋ : k ≥ 1}` and `d_i = 2` when `i` lies in the Beatty sequence of `β`
(for complementary `α`, `β` every `i ≥ 1` gets exactly one digit). Following the octal-code
rules, a heap of size `n` with `d_n = 1` may be removed entirely, and `i` tokens with `d_i = 2`
may be removed from a heap of size `n > i`, leaving `n - i` tokens.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 1.1 (octal codes) and
the codes of the gold, silver and bronze games in Sections 2, 3, 4. -/
def beattyOctalMove (α β : ℝ) (n m : ℕ) : Prop :=
  (0 < n ∧ (∃ k : ℤ, 0 < k ∧ beattySeq α k = n) ∧ m = 0) ∨
    ∃ i : ℕ, (∃ k : ℤ, 0 < k ∧ beattySeq β k = i) ∧ 0 < i ∧ i < n ∧ m = n - i

/-- Every move of a Beatty octal game decreases the heap, so the game terminates.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 1.1. -/
theorem beattyOctalMove_lt {α β : ℝ} {n m : ℕ} (h : beattyOctalMove α β n m) : m < n := by
  rcases h with ⟨hn, -, rfl⟩ | ⟨i, -, hi, hin, rfl⟩ <;> omega

/-- For the greedy representation `t = ∑_{k=0}^{n} a_{2k+1} F_{2k+1}` of Theorem 1 (here `a k` is
the paper's `a_{2k+1}`), `⌊tφ⌋ = ∑ a_{2k+1} F_{2k+2}` and `⌊t(1 + φ)⌋ = ∑ a_{2k+1} F_{2k+3}`.
Greedy is stated by partial sums (`∑_{k<m} a_{2k+1} F_{2k+1} < F_{2m+1}` for `m ≤ n + 1`); `n`
need not be minimal and `t = 0` is allowed.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 2. -/
theorem_wanted floor_greedy_odd_fib_sum_mul_goldenRatio (n : ℕ) (a : ℕ → ℕ)
    (ha : ∀ m ≤ n + 1, ∑ k ∈ range m, a k * Nat.fib (2 * k + 1) < Nat.fib (2 * m + 1)) :
    ⌊((∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 1) : ℕ) : ℝ) * Real.goldenRatio⌋₊ =
        ∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 2) ∧
      ⌊((∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 1) : ℕ) : ℝ) * (1 + Real.goldenRatio)⌋₊ =
        ∑ k ∈ range (n + 1), a k * Nat.fib (2 * k + 3)

/-- The P-positions of the gold game (octal code `0·d₁d₂…`, `d_i = 1` on the Beatty sequence of
`φ`, `d_i = 2` on that of `1 + φ`) are the heaps of size `0, F_3, F_5, F_7, …`: this set is
stable (no move between two of its members) and absorbing (every other heap has a move into
it), which determines the P-positions (`MetaMathlibExt.pPositions_unique`).

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 3. -/
theorem_wanted goldGame_pPositions (P : Set ℕ)
    (hP : ∀ x, x ∈ P ↔ x = 0 ∨ ∃ k, 1 ≤ k ∧ x = Nat.fib (2 * k + 1)) :
    (∀ x y, x ∈ P → beattyOctalMove Real.goldenRatio (1 + Real.goldenRatio) x y → y ∉ P) ∧
      ∀ x, x ∉ P → ∃ y, beattyOctalMove Real.goldenRatio (1 + Real.goldenRatio) x y ∧ y ∈ P

/-- Let `R_k = P_k` for odd `k`, `R_k = H_k` for even `k`, and `R'_k = H_k` for odd `k`,
`R'_k = P_k` for even `k`. For the greedy representation `t = ∑_{k=1}^{n} a_k R_k` of Theorem 5,
`⌊t(1 + √2)⌋ = ∑_{k=1}^{n} a_k R'_{k+1}`. Greedy is stated by partial sums
(`∑_{1≤k<m} a_k R_k < R_m` for `1 ≤ m ≤ n + 1`); `n` need not be minimal.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 6 (1). -/
theorem_wanted floor_greedy_pell_halfCompanion_sum_mul_one_add_sqrt_two (R R' : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then pellNumber k else pellLucasSequence k)
    (hR' : ∀ k, R' k = if k % 2 = 1 then pellLucasSequence k else pellNumber k)
    (n : ℕ) (a : ℕ → ℕ)
    (ha : ∀ m, 1 ≤ m → m ≤ n + 1 → ∑ k ∈ Ico 1 m, a k * R k < R m) :
    ⌊((∑ k ∈ Icc 1 n, a k * R k : ℕ) : ℝ) * (1 + Real.sqrt 2)⌋₊ =
      ∑ k ∈ Icc 1 n, a k * R' (k + 1)

/-- Let `R_k = 2P_k` for odd `k`, `R_k = H_k` for even `k`, and `R'_k = P_k` for odd `k`,
`R'_k = H_k` for even `k`. For the greedy representation `t = ∑_{k=0}^{n} a_k R_k` of Theorem 4,
`⌊t (2 + √2) / 2⌋ = ∑_{k=0}^{n} a_k R'_{k+1}`. Greedy is stated by partial sums
(`∑_{k<m} a_k R_k < R_m` for `m ≤ n + 1`); `n` need not be minimal.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 6 (2). -/
theorem_wanted floor_greedy_two_pell_halfCompanion_sum_mul (R R' : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k)
    (hR' : ∀ k, R' k = if k % 2 = 1 then pellNumber k else pellLucasSequence k)
    (n : ℕ) (a : ℕ → ℕ) (ha : ∀ m ≤ n + 1, ∑ k ∈ range m, a k * R k < R m) :
    ⌊((∑ k ∈ range (n + 1), a k * R k : ℕ) : ℝ) * ((2 + Real.sqrt 2) / 2)⌋₊ =
      ∑ k ∈ range (n + 1), a k * R' (k + 1)

/-- The P-positions of the silver game (octal code `0·d₁d₂…`, `d_i = 1` on the Beatty sequence
of `1 + √2`, `d_i = 2` on that of `(2 + √2) / 2`) are the heaps of size
`0, P_1, H_2, P_3, H_4, …`: this set is stable and absorbing for the moves of the game, which
determines the P-positions (`MetaMathlibExt.pPositions_unique`).

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 7. -/
theorem_wanted silverGame_pPositions (P : Set ℕ)
    (hP : ∀ x, x ∈ P ↔
      x = 0 ∨ ∃ k, x = pellNumber (2 * k + 1) ∨ x = pellLucasSequence (2 * k + 2)) :
    (∀ x y, x ∈ P → beattyOctalMove (1 + Real.sqrt 2) ((2 + Real.sqrt 2) / 2) x y → y ∉ P) ∧
      ∀ x, x ∉ P → ∃ y, beattyOctalMove (1 + Real.sqrt 2) ((2 + Real.sqrt 2) / 2) x y ∧ y ∈ P

/-- With `α = (3 + √13) / 2`, `β = (5 + √13) / 6` and `γ = (√13 - 3) / 2`, for `k ≥ 0`:
(1) `B_{2k+1} α = B_{2k+2} + γ^{2k+1}`;
(2) `C_{2k} α = C_{2k+1} + (13 + √13) / (2√13) · γ^{2k}`;
(3) `D_{2k} α = D_{2k+1} + (13 - √13) / (2√13) · γ^{2k}`;
(4) `3B_{2k+1} β = C_{2k+2} + (13 - 3√13) / (2√13) · γ^{2k}`;
(5) `(B_{2k+1} + C_{2k+2}) β = D_{2k+2} + (65 - 17√13) / (6√13) · γ^{2k}`;
(6) `D_{2k} β = B_{2k+1} + (13 - √13) / (6√13) · γ^{2k}`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Proposition 3. -/
theorem_wanted bronze_mul_metallic_identities (k : ℕ) :
    let α : ℝ := (3 + Real.sqrt 13) / 2
    let β : ℝ := (5 + Real.sqrt 13) / 6
    let γ : ℝ := (Real.sqrt 13 - 3) / 2
    (lucasU bronzeLucasParams (2 * k + 1) : ℝ) * α =
        lucasU bronzeLucasParams (2 * k + 2) + γ ^ (2 * k + 1) ∧
      (bronzeCompanionFirst (2 * k) : ℝ) * α = bronzeCompanionFirst (2 * k + 1) +
        (13 + Real.sqrt 13) / (2 * Real.sqrt 13) * γ ^ (2 * k) ∧
      (bronzeCompanionSecond (2 * k) : ℝ) * α = bronzeCompanionSecond (2 * k + 1) +
        (13 - Real.sqrt 13) / (2 * Real.sqrt 13) * γ ^ (2 * k) ∧
      (3 * lucasU bronzeLucasParams (2 * k + 1) : ℝ) * β = bronzeCompanionFirst (2 * k + 2) +
        (13 - 3 * Real.sqrt 13) / (2 * Real.sqrt 13) * γ ^ (2 * k) ∧
      ((lucasU bronzeLucasParams (2 * k + 1) + bronzeCompanionFirst (2 * k + 2) : ℤ) : ℝ) * β =
        bronzeCompanionSecond (2 * k + 2) +
          (65 - 17 * Real.sqrt 13) / (6 * Real.sqrt 13) * γ ^ (2 * k) ∧
      (bronzeCompanionSecond (2 * k) : ℝ) * β = lucasU bronzeLucasParams (2 * k + 1) +
        (13 - Real.sqrt 13) / (6 * Real.sqrt 13) * γ ^ (2 * k)

/-- Let `R_{3m} = D_{2m}`, `R_{3m+1} = 3B_{2m+1}`, `R_{3m+2} = B_{2m+1} + C_{2m+2}`. Every
positive integer `t` is `∑_{k=0}^{n} a_k R_k` with `R_n ≤ t < R_{n+1}`, `a_k = 0` for `k > n`,
(3) `a_0 ≤ 2`, and `a_0 ≤ 1` if `a_1 = 1` or `a_2 = 1`; (4) for `k > 0`, `a_k ≤ 4` if
`3 ∣ k` and `a_k ≤ 1` otherwise; (5) `a_k = 4` forces `a_{k-1} = a_{k+1} = 0`, `a_{k-3} < 4`,
`a_{k+3} < 4`; (6) `a_{3m+1}`, `a_{3m+2}` are not both `1`; (7) if `a_{3m} = 3` (`m ≥ 1`), then
`a_{3m+1} = 1` or `a_{3m+2} = 1` forces `a_{3m-1} = a_{3m-2} = 0`, and `a_{3m-1} = 1` or
`a_{3m-2} = 1` forces `a_{3m+1} = a_{3m+2} = 0` ("vice-versa").

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 8. -/
theorem_wanted exists_mixed_bronze_representation (R : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 0 then bronzeCompanionSecond (2 * (k / 3))
      else if k % 3 = 1 then 3 * lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else lucasU bronzeLucasParams (2 * (k / 3) + 1) + bronzeCompanionFirst (2 * (k / 3) + 2))
    {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), R n ≤ t ∧ (t : ℤ) < R (n + 1) ∧
      (t : ℤ) = ∑ k ∈ range (n + 1), (a k : ℤ) * R k ∧ (∀ k, n < k → a k = 0) ∧
      a 0 ≤ 2 ∧ ((a 1 = 1 ∨ a 2 = 1) → a 0 ≤ 1) ∧
      (∀ k, 0 < k → (k % 3 = 0 → a k ≤ 4) ∧ (k % 3 ≠ 0 → a k ≤ 1)) ∧
      (∀ k, a k = 4 → a (k - 1) = 0 ∧ a (k + 1) = 0 ∧ a (k - 3) < 4 ∧ a (k + 3) < 4) ∧
      (∀ m, (a (3 * m + 1) = 1 → a (3 * m + 2) = 0) ∧ (a (3 * m + 2) = 1 → a (3 * m + 1) = 0)) ∧
      ∀ m, 1 ≤ m → a (3 * m) = 3 →
        ((a (3 * m + 1) = 1 ∨ a (3 * m + 2) = 1) → a (3 * m - 1) = 0 ∧ a (3 * m - 2) = 0) ∧
        ((a (3 * m - 1) = 1 ∨ a (3 * m - 2) = 1) → a (3 * m + 1) = 0 ∧ a (3 * m + 2) = 0)

/-- Let `R_{3m+1} = B_{2m+1}`, `R_{3m+2} = C_{2m+2}`, `R_{3m} = D_{2m}`. Every positive integer
`t` is `∑_{k=1}^{n} a_k R_k` with `R_n ≤ t < R_{n+1}`, `a_k = 0` for `k > n`, (3) `a_1 ≤ 3`,
and `a_2 = a_3 = 0` if `a_1 = 3`; (4) for `k > 1`, `a_k ≤ 4` if `k ≡ 1 (mod 3)` and `a_k ≤ 1`
otherwise; (5) `a_k = 4` forces `a_{k-1} = a_{k+1} = 0`, `a_{k-3} < 4`, `a_{k+3} < 4`.
The paper's conditions (6) and (7) are omitted: no representation of `50` satisfies (6)
together with (2)–(5), and the greedy representation `410 = 3B_5 + D_4 + D_2` (`327 + 76 + 7`;
digits `a_7 = 3`, `a_6 = 1`, `a_3 = 1`) violates (7).

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 9 (1)–(5). -/
theorem_wanted exists_bronze_companion_representation (R : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
      else bronzeCompanionSecond (2 * (k / 3)))
    {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), 1 ≤ n ∧ R n ≤ t ∧ (t : ℤ) < R (n + 1) ∧
      (t : ℤ) = ∑ k ∈ Icc 1 n, (a k : ℤ) * R k ∧ (∀ k, n < k → a k = 0) ∧
      a 1 ≤ 3 ∧ (a 1 = 3 → a 2 = 0 ∧ a 3 = 0) ∧
      (∀ k, 1 < k → (k % 3 = 1 → a k ≤ 4) ∧ (k % 3 ≠ 1 → a k ≤ 1)) ∧
      ∀ k, a k = 4 → a (k - 1) = 0 ∧ a (k + 1) = 0 ∧ a (k - 3) < 4 ∧ a (k + 3) < 4

/-- Let `R_{3m+1} = B_{2m+1}`, `R_{3m+2} = C_{2m+2}`, `R_{3m} = D_{2m}` and
`R'_{3m+1} = D_{2m+1}`, `R'_{3m+2} = B_{2m+2}`, `R'_{3m} = C_{2m+1}`. For the greedy
representation `t = ∑_{k=1}^{n} a_k R_k` of Theorem 9, `⌊t (3 + √13) / 2⌋ = ∑ a_k R'_{k+1}`.
Greedy is stated by partial sums (`∑_{1≤k<m} a_k R_k < R_m` for `1 ≤ m ≤ n + 1`); `n` need not
be minimal.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 10 (1). -/
theorem_wanted floor_greedy_bronze_companion_sum_mul (R R' : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
      else bronzeCompanionSecond (2 * (k / 3)))
    (hR' : ∀ k, R' k =
      if k % 3 = 1 then bronzeCompanionSecond (2 * (k / 3) + 1)
      else if k % 3 = 2 then lucasU bronzeLucasParams (2 * (k / 3) + 2)
      else bronzeCompanionFirst (2 * (k / 3) + 1))
    (n : ℕ) (a : ℕ → ℕ)
    (ha : ∀ m, 1 ≤ m → m ≤ n + 1 → ∑ k ∈ Ico 1 m, (a k : ℤ) * R k < R m) :
    ⌊((∑ k ∈ Icc 1 n, (a k : ℤ) * R k : ℤ) : ℝ) * ((3 + Real.sqrt 13) / 2)⌋ =
      ∑ k ∈ Icc 1 n, (a k : ℤ) * R' (k + 1)

/-- Let `R_{3m} = D_{2m}`, `R_{3m+1} = 3B_{2m+1}`, `R_{3m+2} = B_{2m+1} + C_{2m+2}` and
`R'_{3m} = D_{2m}`, `R'_{3m+1} = B_{2m+1}`, `R'_{3m+2} = C_{2m+2}`. For the greedy representation
`t = ∑_{k=0}^{n} a_k R_k` of Theorem 8, `⌊t (5 + √13) / 6⌋ = ∑ a_k R'_{k+1}`. Greedy is stated
by partial sums (`∑_{k<m} a_k R_k < R_m` for `m ≤ n + 1`); `n` need not be minimal.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 10 (2). -/
theorem_wanted floor_greedy_mixed_bronze_sum_mul (R R' : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 0 then bronzeCompanionSecond (2 * (k / 3))
      else if k % 3 = 1 then 3 * lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else lucasU bronzeLucasParams (2 * (k / 3) + 1) + bronzeCompanionFirst (2 * (k / 3) + 2))
    (hR' : ∀ k, R' k =
      if k % 3 = 0 then bronzeCompanionSecond (2 * (k / 3))
      else if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else bronzeCompanionFirst (2 * (k / 3) + 2))
    (n : ℕ) (a : ℕ → ℕ) (ha : ∀ m ≤ n + 1, ∑ k ∈ range m, (a k : ℤ) * R k < R m) :
    ⌊((∑ k ∈ range (n + 1), (a k : ℤ) * R k : ℤ) : ℝ) * ((5 + Real.sqrt 13) / 6)⌋ =
      ∑ k ∈ range (n + 1), (a k : ℤ) * R' (k + 1)

/-- The P-positions of the bronze game (octal code `0·d₁d₂…`, `d_i = 1` on the Beatty sequence
of `(3 + √13) / 2`, `d_i = 2` on that of `(5 + √13) / 6`) are the heaps of size
`0, B_1, C_2, D_2, B_3, C_4, D_4, …`: this set is stable and absorbing for the moves of the
game, which determines the P-positions (`MetaMathlibExt.pPositions_unique`).

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 11. -/
theorem_wanted bronzeGame_pPositions (P : Set ℕ)
    (hP : ∀ x, x ∈ P ↔ x = 0 ∨ ∃ k, (x : ℤ) = lucasU bronzeLucasParams (2 * k + 1) ∨
      (x : ℤ) = bronzeCompanionFirst (2 * k + 2) ∨ (x : ℤ) = bronzeCompanionSecond (2 * k + 2)) :
    (∀ x y, x ∈ P →
        beattyOctalMove ((3 + Real.sqrt 13) / 2) ((5 + Real.sqrt 13) / 6) x y → y ∉ P) ∧
      ∀ x, x ∉ P →
        ∃ y, beattyOctalMove ((3 + Real.sqrt 13) / 2) ((5 + Real.sqrt 13) / 6) x y ∧ y ∈ P

end

end MetaMathlibExt
