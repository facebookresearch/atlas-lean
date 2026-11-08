/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.List.GetD

namespace MetaMathlibExt

@[expose] public section

/-! # A three-term Hofstadter-like recurrence

The recurrence `B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))`, run from a finite list
of initial conditions `B(1), …, B(m)`. With `pad = true` the sequence is also defined to be `0`
at every nonpositive index (the source's `⟨0̄; …⟩` convention). A term that would reference an
undefined index (a nonpositive index when `pad = false`, or an index not yet computed) cannot
be computed, and the sequence stops there: it "dies" (unpadded) or "ends" (padded).
-/

/-- The value at index `j` of the sequence whose first terms are `xs = #[B(1), …, B(m)]`:
`xs[j - 1]` for `1 ≤ j ≤ m`, `0` for `j ≤ 0` when `pad`, and undefined otherwise.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1
(initial-condition and sequence-death conventions). -/
def threeTermHofstadterLookup (pad : Bool) (xs : Array ℤ) (j : ℤ) : Option ℤ :=
  if j ≤ 0 then (if pad then some 0 else none) else xs[(j - 1).toNat]?

/-- The next term `B(m + 1) = B(m+1 - B(m)) + B(m+1 - B(m-1)) + B(m+1 - B(m-2))` after
`xs = #[B(1), …, B(m)]`, or `none` when it references an undefined index.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
def threeTermHofstadterNext (pad : Bool) (xs : Array ℤ) : Option ℤ :=
  let n : ℤ := xs.size + 1
  (threeTermHofstadterLookup pad xs (n - 1)).bind fun b₁ =>
  (threeTermHofstadterLookup pad xs (n - 2)).bind fun b₂ =>
  (threeTermHofstadterLookup pad xs (n - 3)).bind fun b₃ =>
  (threeTermHofstadterLookup pad xs (n - b₁)).bind fun v₁ =>
  (threeTermHofstadterLookup pad xs (n - b₂)).bind fun v₂ =>
  (threeTermHofstadterLookup pad xs (n - b₃)).map fun v₃ => v₁ + v₂ + v₃

/-- Extend the computed terms `xs` by the next `k` terms of the recurrence (tail-recursive,
appending in place), or `none` if the sequence stops earlier.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
def threeTermHofstadterExtend (pad : Bool) : ℕ → Array ℤ → Option (Array ℤ)
  | 0, xs => some xs
  | k + 1, xs =>
    match threeTermHofstadterNext pad xs with
    | none => none
    | some v => threeTermHofstadterExtend pad k (xs.push v)

/-- The initial conditions followed by the next `k` terms of the recurrence, or `none` if
the sequence stops earlier.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
def threeTermHofstadterPrefix (pad : Bool) (init : List ℤ) (k : ℕ) : Option (Array ℤ) :=
  threeTermHofstadterExtend pad k init.toArray

/-- The term `B(j)` of the sequence with initial conditions `init`, or `none` if the
sequence stops before index `j`. Index `0` follows `threeTermHofstadterLookup`: it is `0`
when `pad` and undefined otherwise.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
def threeTermHofstadterTerm (pad : Bool) (init : List ℤ) (j : ℕ) : Option ℤ :=
  (threeTermHofstadterPrefix pad init (j - init.length)).bind fun xs =>
    threeTermHofstadterLookup pad xs j

/-- The sequence with initial conditions `init` has exactly `T` terms: its first `T` terms
exist and the term at index `T + 1` cannot be computed.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1
("dies after `n - 1` terms"; "ends" in the padded case). -/
def ThreeTermHofstadterEndsAfter (pad : Bool) (init : List ℤ) (T : ℕ) : Prop :=
  ∃ xs, threeTermHofstadterPrefix pad init (T - init.length) = some xs ∧ xs.size = T ∧
    threeTermHofstadterNext pad xs = none

/-- The initial conditions are the first terms.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
theorem threeTermHofstadterTerm_of_le_length (pad : Bool) (init : List ℤ) {j : ℕ}
    (hj : j ≤ init.length) :
    threeTermHofstadterTerm pad init j = threeTermHofstadterLookup pad init.toArray j := by
  simp [threeTermHofstadterTerm, threeTermHofstadterPrefix, Nat.sub_eq_zero_of_le hj,
    threeTermHofstadterExtend]

/-- Index `0` is `0` in the padded sequence and undefined in the unpadded one.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
theorem threeTermHofstadterTerm_zero :
    threeTermHofstadterTerm true [5] 0 = some 0 ∧ threeTermHofstadterTerm false [5] 0 = none := by
  decide

/-- The `B`-sequence `⟨1, 2, 3, 4, 5⟩` continues with `B(6) = 1 + 2 + 3 = 6` and
`B(7) = B(1) + B(2) + B(3) = 6`.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1. -/
theorem threeTermHofstadterTerm_bSequence_six_seven :
    threeTermHofstadterTerm false [1, 2, 3, 4, 5] 6 = some 6 ∧
      threeTermHofstadterTerm false [1, 2, 3, 4, 5] 7 = some 6 := by
  decide

/-- `B_3 = ⟨1, 2, 3⟩` has `B_3(4) = 6` and then dies: it has exactly four terms.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, proof of
Theorem 1 (`B_3(4) = 6`). -/
theorem threeTermHofstadterEndsAfter_one_two_three :
    ThreeTermHofstadterEndsAfter false [1, 2, 3] 4 :=
  ⟨#[1, 2, 3, 6], rfl, rfl, by decide⟩

/-- For `N = 3`, `N = 4` or `N ≥ 10`, the sequence `B_N` with initial conditions
`⟨1, 2, …, N⟩` (no padding) dies.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 1
(`jis-2024-24.7.4-thm-1`). -/
public theorem_wanted threeTermHofstadter_linear_dies {N : ℕ} (hN : N = 3 ∨ N = 4 ∨ 10 ≤ N) :
    ∃ T, ThreeTermHofstadterEndsAfter false ((List.range N).map fun i : ℕ => (i : ℤ) + 1) T

/-- For `N ≥ 14`, the sequence `B_N` with initial conditions `⟨1, 2, …, N⟩` has exactly
`N + 24` terms.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 1
(`jis-2024-24.7.4-thm-1`). -/
public theorem_wanted threeTermHofstadter_linear_length {N : ℕ} (hN : 14 ≤ N) :
    ThreeTermHofstadterEndsAfter false ((List.range N).map fun i : ℕ => (i : ℤ) + 1) (N + 24)

/-- For `N ≥ 72`, the padded sequence `B_{N̄}` with initial conditions
`⟨0̄; 1, 2, …, N⟩` follows the period-`7` pattern
`B(N+7k) = 7k+2`, `B(N+7k+1) = N+7k+2`, `B(N+7k+2) = N+7k+4`, `B(N+7k+3) = 7`,
`B(N+7k+4) = 2N+2k+45`, `B(N+7k+5) = 2N+k-7`, `B(N+7k+6) = N-2` (`k ≥ 1`) from index
`N + 67` through index `2N + ν`, where `ν = -1, -2, -2, -2, 2, 1, 0` for
`N ≡ 0, 1, …, 6 (mod 7)`.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 2
(`jis-2024-24.7.4-thm-2`). -/
public theorem_wanted threeTermHofstadter_padded_linear_period_seven {N : ℕ} (hN : 72 ≤ N)
    (k r : ℕ) (hk : 1 ≤ k) (hr : r < 7) (hlo : N + 67 ≤ N + 7 * k + r)
    (hhi : ((N + 7 * k + r : ℕ) : ℤ) ≤ 2 * N + [-1, -2, -2, -2, 2, 1, 0].getD (N % 7) 0) :
    threeTermHofstadterTerm true ((List.range N).map fun i : ℕ => (i : ℤ) + 1) (N + 7 * k + r) =
      some ([7 * k + 2, N + 7 * k + 2, N + 7 * k + 4, 7, 2 * N + 2 * k + 45, 2 * N + k - 7,
        N - 2].getD r 0 : ℤ)

/-- The padded sequence `B_{N̄}` with initial conditions `⟨0̄; 1, 2, …, N⟩` ends after
`2N + e` terms once `N ≥ t`, where for `N ≡ 0, 1, …, 6 (mod 7)` the thresholds are
`t = 196, 2087, 3201, 4315, 200, 32478, 118` and the offsets are
`e = 27, 254, 524, 560, 20, 4547, 9`.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 2
(`jis-2024-24.7.4-thm-2`). -/
public theorem_wanted threeTermHofstadter_padded_linear_endsAfter {N : ℕ}
    (hN : [196, 2087, 3201, 4315, 200, 32478, 118].getD (N % 7) 0 ≤ N) :
    ThreeTermHofstadterEndsAfter true ((List.range N).map fun i : ℕ => (i : ℤ) + 1)
      (2 * N + [27, 254, 524, 560, 20, 4547, 9].getD (N % 7) 0)

/-- Seven-cycle lemma. Let `K ≥ 7`, `c ≥ 1`, `0 ≤ γ ≤ 6`, `L = K - 7c - γ ≥ 0`,
`M = K + L + 5`, and let `λ ≥ -2c + (2, 1, 4, 3, 2, 1, 0)_γ` and `μ ≥ -c + (0, 0, 3, 2, 1, 0, -1)_γ`.
For arbitrary integers `a_1, …, a_L`, the padded sequence with initial conditions
`⟨0̄; 1, 2, …, K, 6, a_1, …, a_L, 2K+λ-2, 2K+μ-1, K-2⟩` satisfies
`B(M+7k) = L+7k+7`, `B(M+7k+1) = M+7k+2`, `B(M+7k+2) = M+7k+4`, `B(M+7k+3) = 7`,
`B(M+7k+4) = 2K+2k+λ`, `B(M+7k+5) = 2K+k+μ`, `B(M+7k+6) = K-2` from index `M - 3` through
index `2K + ν`, `ν = (-2, -2, 2, 1, 0, -1, -2)_γ`.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 3
(`jis-2024-24.7.4-lem-3`). -/
public theorem_wanted threeTermHofstadter_sevenCycle {K c γ : ℕ} (hK : 7 ≤ K) (hc : 1 ≤ c)
    (hγ : γ ≤ 6) (hL : 7 * c + γ ≤ K) {lam mu : ℤ}
    (hlam : -2 * (c : ℤ) + [2, 1, 4, 3, 2, 1, 0].getD γ 0 ≤ lam)
    (hmu : -(c : ℤ) + [0, 0, 3, 2, 1, 0, -1].getD γ 0 ≤ mu)
    (a : List ℤ) (ha : a.length = K - 7 * c - γ) (k : ℤ) (r : ℕ) (hr : r < 7)
    (hlo : ((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) - 3 ≤ (2 * K - 7 * c - γ + 5 : ℕ) + 7 * k + r)
    (hhi : ((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) + 7 * k + r ≤
      2 * K + [-2, -2, 2, 1, 0, -1, -2].getD γ 0) :
    threeTermHofstadterTerm true
        ((List.range K).map (fun i : ℕ => (i : ℤ) + 1) ++ [6] ++ a ++
          [2 * K + lam - 2, 2 * K + mu - 1, K - 2])
        (((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) + 7 * k + r).toNat =
      some ([((K - 7 * c - γ : ℕ) : ℤ) + 7 * k + 7, ((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) + 7 * k + 2,
        ((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) + 7 * k + 4, 7, 2 * K + 2 * k + lam, 2 * K + k + mu,
        K - 2].getD r 0)

/-- Two-cycle lemma. Let `K ≥ 1` and `M ≥ K + 5`. For arbitrary integers `a_1, …, a_K`, the
padded sequence with initial conditions `⟨0̄; a_1, …, a_K, 2, M, 2⟩` satisfies
`B(K+2k+1) = 2` for all `k ≥ 0` and `B(K+2k) = 2^(k-1) M` for all `k ≥ 1` (forever).

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 4,
citing the author's thesis, Proposition 9.9 (`jis-2024-24.7.4-lem-4`). -/
public theorem_wanted threeTermHofstadter_twoCycle {K : ℕ} (hK : 1 ≤ K) {M : ℤ}
    (hM : (K : ℤ) + 5 ≤ M) (a : List ℤ) (ha : a.length = K) (k : ℕ) :
    threeTermHofstadterTerm true (a ++ [2, M, 2]) (K + 2 * k + 1) = some 2 ∧
      (1 ≤ k → threeTermHofstadterTerm true (a ++ [2, M, 2]) (K + 2 * k) =
        some (2 ^ (k - 1) * M))

/-- Five-cycle lemma. Let `K ≥ 3` and `μ ≥ 1`. For arbitrary integers `a_4, …, a_K`, the
padded sequence with initial conditions `⟨0̄; 1, 2, 3, a_4, …, a_K, K+μ, 3, K+3, K+μ+1, 5⟩`
satisfies `B(K+5k) = 5`, `B(K+5k+1) = K+3k+μ`, `B(K+5k+2) = 3`, `B(K+5k+3) = K+5k+3`,
`B(K+5k+4) = K+3k+μ+1` from index `K + 1` through index `K + ⌊(5μ - 15)/2⌋`.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 5,
citing the author's thesis, Proposition 9.10 (`jis-2024-24.7.4-lem-5`). -/
public theorem_wanted threeTermHofstadter_fiveCycle {K : ℕ} (hK : 3 ≤ K) {mu : ℤ} (hmu : 1 ≤ mu)
    (a : List ℤ) (ha : a.length = K - 3) (k r : ℕ) (hr : r < 5) (hlo : K + 1 ≤ K + 5 * k + r)
    (hhi : ((K + 5 * k + r : ℕ) : ℤ) ≤ K + (5 * mu - 15) / 2) :
    threeTermHofstadterTerm true ([1, 2, 3] ++ a ++ [K + mu, 3, K + 3, K + mu + 1, 5])
        (K + 5 * k + r) =
      some ([5, K + 3 * k + mu, 3, K + 5 * k + 3, K + 3 * k + mu + 1].getD r 0 : ℤ)

/-- Second sixteen-cycle lemma. Let `K, λ, μ₁, μ₂, γ₁, γ₂, γ₃` be positive integers with
`λ > 31 + K` and `μ₁, μ₂, γ₁, γ₂, γ₃ > λ`. For arbitrary integers `a_1, …, a_K`, the padded
sequence with initial conditions
`⟨0̄; a_1, …, a_K, 16, μ₂, 7, γ₂, λ, 16, λ, 16, μ₁, 10, γ₃, μ₂, 7, λ, 16, γ₁⟩` satisfies, from
index `K + 1` through index `λ`, `B(K+16k) = μ₁ 2^k + γ₁ - 2μ₁`, `B(K+16k+1) = 16`,
`B(K+16k+2) = μ₂ 2^k`, `B(K+16k+3) = 7`, `B(K+16k+4) = 7k + γ₂`, `B(K+16k+5) = λ`,
`B(K+16k+6) = 16`, `B(K+16k+7) = λ`, `B(K+16k+8) = 16`, `B(K+16k+9) = μ₁ 2^k`,
`B(K+16k+10) = 10`, `B(K+16k+11) = 16k + γ₃`, `B(K+16k+12) = μ₂ 2^k`, `B(K+16k+13) = 7`,
`B(K+16k+14) = λ`, `B(K+16k+15) = 16`.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 7,
citing the author's thesis, Proposition 9.16 (`jis-2024-24.7.4-lem-7`). -/
public theorem_wanted threeTermHofstadter_sixteenCycle_two {K : ℕ} (hK : 1 ≤ K)
    {lam mu₁ mu₂ ga₁ ga₂ ga₃ : ℤ} (hlam : 31 + (K : ℤ) < lam) (hmu₁ : lam < mu₁)
    (hmu₂ : lam < mu₂) (hga₁ : lam < ga₁) (hga₂ : lam < ga₂) (hga₃ : lam < ga₃)
    (a : List ℤ) (ha : a.length = K) (k r : ℕ) (hr : r < 16) (hlo : K + 1 ≤ K + 16 * k + r)
    (hhi : ((K + 16 * k + r : ℕ) : ℤ) ≤ lam) :
    threeTermHofstadterTerm true
        (a ++ [16, mu₂, 7, ga₂, lam, 16, lam, 16, mu₁, 10, ga₃, mu₂, 7, lam, 16, ga₁])
        (K + 16 * k + r) =
      some ([mu₁ * 2 ^ k + ga₁ - 2 * mu₁, 16, mu₂ * 2 ^ k, 7, 7 * k + ga₂, lam, 16, lam, 16,
        mu₁ * 2 ^ k, 10, 16 * k + ga₃, mu₂ * 2 ^ k, 7, lam, 16].getD r 0)

/-- First sixteen-cycle lemma. Let `K, λ, μ₁, μ₂, γ` be positive integers with `λ > 31 + K` and
`μ₁, μ₂, γ > λ`. For arbitrary integers `a_1, …, a_K`, the padded sequence with initial
conditions `⟨0̄; a_1, …, a_K, λ, 7, μ₂, 16, μ₂, 16, μ₁, λ, 7, μ₂, 16, 2μ₂, 16, μ₂, 25, γ, λ, 7⟩`
satisfies, from index `K + 1` through index `λ`, `B(K+16k) = μ₁ 2^{k-1} + γ - μ₁`,
`B(K+16k+1) = λ`, `B(K+16k+2) = 7`, `B(K+16k+3) = μ₂ 2^k`, `B(K+16k+4) = 16`,
`B(K+16k+5) = μ₂ 2^k`, `B(K+16k+6) = 16`, `B(K+16k+7) = μ₁ 2^k`, `B(K+16k+8) = λ`,
`B(K+16k+9) = 7`, `B(K+16k+10) = μ₂ 2^k`, `B(K+16k+11) = 16`, `B(K+16k+12) = μ₂ 2^{k+1}`,
`B(K+16k+13) = 16`, `B(K+16k+14) = μ₂ 2^k`, `B(K+16k+15) = 25`.
Corrected: the paper prints `B(K+16k+12) = μ₂ 2^k`, which contradicts its own initial value
`B(K+12) = 2μ₂`; the exponent `k+1` matches the initial conditions and every later term.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 6,
citing the author's thesis, Proposition 9.13 (`jis-2024-24.7.4-lem-6`). -/
public theorem_wanted threeTermHofstadter_sixteenCycle_one {K : ℕ} (hK : 1 ≤ K)
    {lam mu₁ mu₂ ga : ℤ} (hlam : 31 + (K : ℤ) < lam) (hmu₁ : lam < mu₁) (hmu₂ : lam < mu₂)
    (hga : lam < ga) (a : List ℤ) (ha : a.length = K) (k r : ℕ) (hr : r < 16)
    (hlo : K + 1 ≤ K + 16 * k + r) (hhi : ((K + 16 * k + r : ℕ) : ℤ) ≤ lam) :
    threeTermHofstadterTerm true
        (a ++ [lam, 7, mu₂, 16, mu₂, 16, mu₁, lam, 7, mu₂, 16, 2 * mu₂, 16, mu₂, 25, ga, lam, 7])
        (K + 16 * k + r) =
      some ([mu₁ * 2 ^ (k - 1) + ga - mu₁, lam, 7, mu₂ * 2 ^ k, 16, mu₂ * 2 ^ k, 16,
        mu₁ * 2 ^ k, lam, 7, mu₂ * 2 ^ k, 16, mu₂ * 2 ^ (k + 1), 16, mu₂ * 2 ^ k, 25].getD r 0)

end

end MetaMathlibExt
