/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Nth
public import Mathlib.Order.LiminfLimsup
public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord
public import MathlibExt.Combinatorics.InfiniteWord.WordFactorComplexity
public import WantedExt.Combinatorics.Words.MetaAutomaticSequencesWanted

/-! # Irvine's conjecture on Gutkovskiy's sequence (Shallit)

Statements from Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*,
INTEGERS 24 (2024), Article A51. Letters `0, 1` of Kimberling's word are `false, true`, and
the word `k = k₁k₂⋯` is indexed from `0` (`kimberlingWord i = k_{i+1}`, the paper's `k'_i`);
the paper's convention `k₀ = 0` only shifts indices. The numbers `K_n = |K_n|` are the lengths
`(kimberlingBlock n).length`.
-/

namespace MetaMathlibExt

open Filter

@[expose] public section

/-- Kimberling's morphism `h` on `{0, 1}` (`false = 0`, `true = 1`): `h(1) = 110`, `h(0) = 11`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1 and Section 2 (the morphism `h`). -/
public def kimberlingMorphism : Bool → List Bool
  | true => [true, true, false]
  | false => [true, true]

/-- The block `K_n = h^n(1)`, so `K₀ = 1`, `K₁ = 110`, `K₂ = 11011011`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2 (`K_n = h^n(1)`). -/
public def kimberlingBlock (n : ℕ) : List Bool :=
  morphIterate kimberlingMorphism n [true]

/-- `K₁ = 110`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem kimberlingBlock_one : kimberlingBlock 1 = [true, true, false] := rfl

/-- `K₂ = 11011011`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem kimberlingBlock_two :
    kimberlingBlock 2 = [true, true, false, true, true, false, true, true] := rfl

/-- `K_n` is a prefix of `K_{n+1}`: `h(1) = 110` starts with `1`, so `h^n(1)` is a prefix of
`h^n(110) = h^{n+1}(1)`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem kimberlingBlock_prefix_succ (n : ℕ) :
    kimberlingBlock n <+: kimberlingBlock (n + 1) := by
  induction n with
  | zero => exact ⟨[true, false], rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨morphExtend kimberlingMorphism t, ?_⟩
    change morphExtend kimberlingMorphism (kimberlingBlock n) ++ _ =
      morphExtend kimberlingMorphism (kimberlingBlock (n + 1))
    rw [← ht, morphExtend_append]

/-- `K_m` is a prefix of `K_n` for `m ≤ n`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem kimberlingBlock_prefix {m n : ℕ} (h : m ≤ n) :
    kimberlingBlock m <+: kimberlingBlock n := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (kimberlingBlock_prefix_succ _)

/-- `|K_n| ≥ 2^n`: every image of `h` has length at least `2`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem two_pow_le_length_kimberlingBlock (n : ℕ) :
    2 ^ n ≤ (kimberlingBlock n).length := by
  have hext : ∀ w : List Bool, 2 * w.length ≤ (morphExtend kimberlingMorphism w).length := by
    intro w
    induction w with
    | nil => simp [morphExtend]
    | cons b w ih =>
      have e : morphExtend kimberlingMorphism (b :: w) =
          kimberlingMorphism b ++ morphExtend kimberlingMorphism w := rfl
      rw [e, List.length_append, List.length_cons]
      cases b <;> simp [kimberlingMorphism] <;> omega
  induction n with
  | zero => simp [kimberlingBlock, morphIterate]
  | succ n ih =>
    have := hext (kimberlingBlock n)
    change _ ≤ (morphExtend kimberlingMorphism (kimberlingBlock n)).length
    rw [pow_succ]
    omega

/-- Kimberling's word `k = k₁k₂k₃⋯ = 1101101111⋯` (OEIS A285431), the common extension of the
blocks `K_n`, indexed from `0`: `kimberlingWord i = k_{i+1}`. The letter is read from
`K_{⌊log₂ i⌋ + 1}`, which has length at least `2^(⌊log₂ i⌋ + 1) > i`; by
`kimberlingWord_eq_getD` every block of length `> i` gives the same letter.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2 (the limit word `k`) and Section 5 (`k'_n = k_{n+1}`). -/
public def kimberlingWord (i : ℕ) : Bool :=
  (kimberlingBlock (Nat.log 2 i + 1)).getD i false

/-- Every block `K_n` with `i < |K_n|` has `kimberlingWord i` at position `i`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem kimberlingWord_eq_getD {i n : ℕ} (hi : i < (kimberlingBlock n).length) :
    kimberlingWord i = (kimberlingBlock n).getD i false := by
  have hi' : i < (kimberlingBlock (Nat.log 2 i + 1)).length :=
    lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) i)
      (two_pow_le_length_kimberlingBlock _)
  unfold kimberlingWord
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
    List.getElem?_eq_getElem hi, Option.getD_some]
  rcases le_total (Nat.log 2 i + 1) n with h | h
  · exact (kimberlingBlock_prefix h).getElem hi'
  · exact ((kimberlingBlock_prefix h).getElem hi).symm

/-- The first letters of `k` are `k₁k₂k₃k₄ = 1101`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Table 1. -/
public theorem kimberlingWord_initial :
    kimberlingWord 0 = true ∧ kimberlingWord 1 = true ∧ kimberlingWord 2 = false ∧
      kimberlingWord 3 = true := by
  decide

/-- Evaluation check: `k₁₀₁ = 0` (OEIS A285431), read from `K₇`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 2. -/
public theorem kimberlingWord_hundred : kimberlingWord 100 = false := by
  decide +kernel

/-- The table `[g₀, …, gₙ]` of Gutkovskiy's sequence, built by course of values: entry `n + 1`
is `(n + 1) - g_{⌊gₙ/2⌋}`, read from the table so far (each step costs one lookup).

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public def gutkovskiyTable : ℕ → Array ℕ
  | 0 => #[0]
  | n + 1 =>
    let a := gutkovskiyTable n
    a.push ((n + 1) - a.getD (a.getD n 0 / 2) 0)

/-- Gutkovskiy's sequence (OEIS A286389): `g₀ = 0` and `gₙ = n - g_{⌊g_{n-1}/2⌋}` for
`n ≥ 1`, evaluated through `gutkovskiyTable`; `gutkovskiy_succ` is the paper's recurrence.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public def gutkovskiy (n : ℕ) : ℕ :=
  (gutkovskiyTable n).getD n 0

/-- `gutkovskiyTable n` has `n + 1` entries.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem size_gutkovskiyTable (n : ℕ) : (gutkovskiyTable n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gutkovskiyTable, ih]

/-- Entry `k ≤ n` of `gutkovskiyTable n` is `g_k`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem getD_gutkovskiyTable {k n : ℕ} (h : k ≤ n) :
    (gutkovskiyTable n).getD k 0 = gutkovskiy k := by
  induction n with
  | zero => obtain rfl : k = 0 := by omega
            rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · rw [← ih (by omega)]
      simp only [gutkovskiyTable, Array.getD_eq_getD_getElem?, Array.getElem?_push,
        size_gutkovskiyTable]
      simp [show k ≠ n + 1 by omega]
    · obtain rfl : k = n + 1 := by omega
      rfl

/-- `gₙ ≤ n`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem gutkovskiy_le (n : ℕ) : gutkovskiy n ≤ n := by
  cases n with
  | zero => decide
  | succ n =>
    have : gutkovskiy (n + 1) = (n + 1) - (gutkovskiyTable n).getD
        ((gutkovskiyTable n).getD n 0 / 2) 0 := by
      simp only [gutkovskiy, gutkovskiyTable, Array.getD_eq_getD_getElem?, Array.getElem?_push,
        size_gutkovskiyTable, ↓reduceIte, Option.getD_some]
    omega

/-- The recurrence `g_{n+1} = (n + 1) - g_{⌊gₙ/2⌋}`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem gutkovskiy_succ (n : ℕ) :
    gutkovskiy (n + 1) = (n + 1) - gutkovskiy (gutkovskiy n / 2) := by
  have h1 : gutkovskiy (n + 1) = (n + 1) - (gutkovskiyTable n).getD
      ((gutkovskiyTable n).getD n 0 / 2) 0 := by
    simp only [gutkovskiy, gutkovskiyTable, Array.getD_eq_getD_getElem?, Array.getElem?_push,
      size_gutkovskiyTable, ↓reduceIte, Option.getD_some]
  rw [h1, getD_gutkovskiyTable le_rfl, getD_gutkovskiyTable
    (le_trans (Nat.div_le_self _ _) (gutkovskiy_le n))]

/-- The first values `g₀, …, g₃ = 0, 1, 2, 2`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Table 1. -/
public theorem gutkovskiy_initial :
    gutkovskiy 0 = 0 ∧ gutkovskiy 1 = 1 ∧ gutkovskiy 2 = 2 ∧ gutkovskiy 3 = 2 := by
  have h0 : gutkovskiy 0 = 0 := rfl
  have h1 : gutkovskiy 1 = 1 := by rw [gutkovskiy_succ, h0, h0]
  have h2 : gutkovskiy 2 = 2 := by rw [gutkovskiy_succ, h1, h0]
  have h3 : gutkovskiy 3 = 2 := by rw [gutkovskiy_succ, h2, h1]
  exact ⟨h0, h1, h2, h3⟩

/-- Evaluation check: `g₁₀₀ = 74` (OEIS A286389).

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 1, Equation (1). -/
public theorem gutkovskiy_hundred : gutkovskiy 100 = 74 := by
  decide +kernel

/-- `A n` (`n ≥ 1`): the position of the `n`-th `1` in `k = k₁k₂⋯`; `A 0 = 0`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 8 (the sequence `A_n`). -/
public noncomputable def kimberlingOnePosition (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun i ↦ kimberlingWord i = true) (n - 1) + 1

/-- `B n` (`n ≥ 1`): the position of the `n`-th `0` in `k = k₁k₂⋯`; `B 0 = 0`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Section 8 (the sequence `B_n`). -/
public noncomputable def kimberlingZeroPosition (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth (fun i ↦ kimberlingWord i = false) (n - 1) + 1

/-- `A₁ = 1`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Table 3. -/
public theorem kimberlingOnePosition_one : kimberlingOnePosition 1 = 1 := by
  simp only [kimberlingOnePosition, one_ne_zero, ↓reduceIte, Nat.sub_self]
  rw [Nat.nth_zero_of_zero (p := fun i ↦ kimberlingWord i = true) kimberlingWord_initial.1]

/-- `B₁ = 3`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Table 3. -/
public theorem kimberlingZeroPosition_one : kimberlingZeroPosition 1 = 3 := by
  have hc : Nat.count (fun i ↦ kimberlingWord i = false) 2 = 0 := by decide
  have h := Nat.nth_count (p := fun i ↦ kimberlingWord i = false) kimberlingWord_initial.2.2.1
  rw [hc] at h
  simp only [kimberlingZeroPosition, one_ne_zero, ↓reduceIte, Nat.sub_self]
  rw [h]

/-- For `n ≥ 2`, `K_n = K_{n-1} K_{n-1} K_{n-2} K_{n-2}`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Proposition 1 (`integers-2024-A51-prop-1`). -/
public theorem_wanted kimberlingBlock_eq_append {n : ℕ} (hn : 2 ≤ n) :
    kimberlingBlock n = kimberlingBlock (n - 1) ++ kimberlingBlock (n - 1) ++
      kimberlingBlock (n - 2) ++ kimberlingBlock (n - 2)

/-- Irvine's conjecture: `gₙ = k₁ + ⋯ + kₙ` for `n ≥ 0`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 1 (`integers-2024-A51-thm-1`). -/
public theorem_wanted gutkovskiy_eq_sum_kimberlingWord (n : ℕ) :
    gutkovskiy n = ∑ i ∈ Finset.range n, (kimberlingWord i).toNat

/-- Closed form: with `α = (√3 - 1)/2` and `β = √3/3`, `gₙ = 2⌊αn⌋ + 1` if the canonical
`K`-representation of `n` ends in `1`, and `gₙ = 2⌊αn + β⌋` if it ends in `0` or `2`. The
representation is a digit list `a = [a₀, a₁, …]` (least significant digit first) with digits in
`{0, 1, 2}`, no two adjacent `2`s, and `n = ∑ aᵢ Kᵢ`; leading zeros are allowed.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 2 (`integers-2024-A51-thm-2`). -/
public theorem_wanted gutkovskiy_eq_two_mul_floor {n : ℕ} {a : List ℕ} (ha : ∀ d ∈ a, d ≤ 2)
    (h22 : ¬ [2, 2] <:+: a)
    (hn : (a.mapIdx fun i d ↦ d * (kimberlingBlock i).length).sum = n) :
    (a.head? = some 1 → (gutkovskiy n : ℤ) = 2 * ⌊(√3 - 1) / 2 * (n : ℝ)⌋ + 1) ∧
      (a.head? = some 0 ∨ a.head? = some 2 →
        (gutkovskiy n : ℤ) = 2 * ⌊(√3 - 1) / 2 * (n : ℝ) + √3 / 3⌋)

/-- For every `n ≥ 1`, `A_{B_n} ∈ {A_n + B_n - 1, A_n + B_n}` (a problem of Fokkink, Ortega
and Rust).

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 3 (`integers-2024-A51-thm-3`). -/
public theorem_wanted kimberlingOnePosition_kimberlingZeroPosition {n : ℕ} (hn : 1 ≤ n) :
    kimberlingOnePosition (kimberlingZeroPosition n) + 1 =
        kimberlingOnePosition n + kimberlingZeroPosition n ∨
      kimberlingOnePosition (kimberlingZeroPosition n) =
        kimberlingOnePosition n + kimberlingZeroPosition n

/-- The sequence `g'ₙ = gₙ mod 2` is the fixed point (the limit of the iterates from `0`) of
the morphism `u : 0 ↦ 01, 1 ↦ 0010` (OEIS A284772). Letters are natural numbers; `u` sends
every nonzero letter to `0010`, which only matters on `1` here.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 4 (`integers-2024-A51-thm-4`). -/
public theorem_wanted isOmegaLimit_gutkovskiy_mod_two :
    IsOmegaLimit (fun b : ℕ ↦ if b = 0 then [0, 1] else [0, 0, 1, 0]) 0
      fun n ↦ gutkovskiy n % 2

/-- `gₙ = 2hₙ + g'ₙ`, where `g'ₙ = gₙ mod 2` and `hₙ = ∑_{0 ≤ i < n} g'ᵢ`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 5 (`integers-2024-A51-thm-5`). -/
public theorem_wanted gutkovskiy_eq_two_mul_sum_mod_two_add (n : ℕ) :
    gutkovskiy n = 2 * ∑ i ∈ Finset.range n, gutkovskiy i % 2 + gutkovskiy n % 2

/-- `k` has exactly two distinct right-special factors of length `n` iff for some `i ≥ 0`,
`x ≤ n < x + K_{2i}` with `x = K₁ + K₃ + ⋯ + K_{2i+1}`, or `y ≤ n < y + K_{2i+1}` with
`y = K₀ + K₂ + ⋯ + K_{2i+2}`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 6 (`integers-2024-A51-thm-6`). -/
public theorem_wanted rightSpecialFactors_kimberlingWord_ncard_eq_two_iff (n : ℕ) :
    (rightSpecialFactors kimberlingWord n).ncard = 2 ↔ ∃ i : ℕ,
      (∑ j ∈ Finset.range (i + 1), (kimberlingBlock (2 * j + 1)).length ≤ n ∧
        n < ∑ j ∈ Finset.range (i + 1), (kimberlingBlock (2 * j + 1)).length +
          (kimberlingBlock (2 * i)).length) ∨
      (∑ j ∈ Finset.range (i + 2), (kimberlingBlock (2 * j)).length ≤ n ∧
        n < ∑ j ∈ Finset.range (i + 2), (kimberlingBlock (2 * j)).length +
          (kimberlingBlock (2 * i + 1)).length)

/-- The subword complexity `ρ(n)` of `k` satisfies `limsup ρ(n)/n = (30 + √3)/23` and
`liminf ρ(n)/n = (3 + √3)/4`.

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Corollary 1 (`integers-2024-A51-cor-1`). -/
public theorem_wanted limsup_liminf_wordFactorComplexity_kimberlingWord :
    limsup (fun n : ℕ ↦ (wordFactorComplexity kimberlingWord n : ℝ) / n) atTop =
        (30 + √3) / 23 ∧
      liminf (fun n : ℕ ↦ (wordFactorComplexity kimberlingWord n : ℝ) / n) atTop =
        (3 + √3) / 4

/-- The critical exponent of `k`, the supremum of `m / p` over the nonempty factors of `k` of
length `m` with period `p ≥ 1`, is `(2√3 + 12)/3`. (Allowing every period, not only the
shortest one, does not change the supremum.)

Source: Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24
(2024), Article A51, Theorem 7 (`integers-2024-A51-thm-7`). -/
public theorem_wanted sSup_exponent_kimberlingWord :
    sSup {e : ℝ | ∃ i m p : ℕ, 0 < m ∧ 0 < p ∧
      (∀ j, j + p < m → kimberlingWord (i + j) = kimberlingWord (i + j + p)) ∧
        e = m / p} = (2 * √3 + 12) / 3

end

end MetaMathlibExt
