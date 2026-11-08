/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Tactic.IntervalCases

/-!
# Algorithms for complementary sequences (wanted statements)

For a sequence `f : ℕ → ℕ` read on the indices `m ≥ 1` (the paper's `f_{¬P}`), the
complementary sequence `f_P` lists the positive integers that are not values `f m`,
`m ≥ 1`. The paper computes its `n`-th term from the counting function
`C_{¬P}(x) = #{m ≥ 1 : f m ≤ x}` or from an easily inverted interleaving function, and
derives closed formulas for the complements of polygonal, second polygonal, centered
polygonal, pyramidal, sum-of-powers and simplex numbers.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The `n`-th (`1`-indexed) positive integer that is not a value `f m` with `m ≥ 1`, i.e. the
paper's `f_P(n)` for the complementary sequence of `f = f_{¬P}`. At `n = 0` it agrees with
`n = 1` (junk value of the `1`-indexing).

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Section 1 (definition of `f_P`). -/
public noncomputable def nthNonValue (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.nth (fun x => 0 < x ∧ ∀ m, 1 ≤ m → f m ≠ x) (n - 1)

/-- Characteristic value: the first positive non-square is `2`.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Section 1 (the non-squares). -/
public theorem nthNonValue_sq_one : nthNonValue (fun m => m ^ 2) 1 = 2 := by
  classical
  have h2 : 0 < 2 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 2 := by
    refine ⟨by norm_num, fun m hm h => ?_⟩
    have : m ≤ 1 := by nlinarith
    interval_cases m
    simp at h
  have hc : Nat.count (fun x => 0 < x ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ x) 2 = 0 := by
    have h0 : ¬ (0 < 0 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 0) := fun h => lt_irrefl 0 h.1
    have h1 : ¬ (0 < 1 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 1) := fun h => h.2 1 le_rfl rfl
    simp only [Nat.count_succ, Nat.count_zero, h0, h1, ite_false]
  have := Nat.nth_count (p := fun x => 0 < x ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ x) h2
  rw [hc] at this
  simpa [nthNonValue] using this

/-- Characteristic value: the second positive non-square is `3`.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Section 1 (the non-squares). -/
public theorem nthNonValue_sq_two : nthNonValue (fun m => m ^ 2) 2 = 3 := by
  classical
  have h2 : 0 < 2 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 2 := by
    refine ⟨by norm_num, fun m hm h => ?_⟩
    have : m ≤ 1 := by nlinarith
    interval_cases m
    simp at h
  have h3 : 0 < 3 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 3 := by
    refine ⟨by norm_num, fun m hm h => ?_⟩
    have : m ≤ 1 := by nlinarith
    interval_cases m
    simp at h
  have hc : Nat.count (fun x => 0 < x ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ x) 3 = 1 := by
    have h0 : ¬ (0 < 0 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 0) := fun h => lt_irrefl 0 h.1
    have h1 : ¬ (0 < 1 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 1) := fun h => h.2 1 le_rfl rfl
    simp only [Nat.count_succ, Nat.count_zero, h0, h1, ite_false,
      eq_true h2, ite_true]
  have := Nat.nth_count (p := fun x => 0 < x ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ x) h3
  rw [hc] at this
  simpa [nthNonValue] using this

/-- Two steps of the Lambek–Moser iteration suffice: if `f(m + 1) - f(m) ≥ m` for all
`m ≥ 1` (and `f(1) ≥ 1`, so that `f` lists positive integers), then
`f_P(n) = n + C(n + C(n))`, where `C(x) = #{m ≥ 1 : f m ≤ x}` is the counting function of
the values of `f`. Under the hypotheses `f m ≥ m`, so only `m ≤ x` can contribute to `C(x)`.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 1. -/
public theorem_wanted nthNonValue_eq_two_step (f : ℕ → ℕ) (hf1 : 1 ≤ f 1)
    (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) (n : ℕ) (hn : 1 ≤ n) :
    let C : ℕ → ℕ := fun x => ((Finset.Icc 1 x).filter (fun m => f m ≤ x)).card
    nthNonValue f n = n + C (n + C n)

/-- One evaluation of the counting function suffices: under the hypotheses of
`nthNonValue_eq_two_step`, `f_P(n) = n + C(n) + 1` if `n + C(n) ≥ f(C(n) + 1)` and
`f_P(n) = n + C(n)` otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 2. -/
public theorem_wanted nthNonValue_eq_one_step (f : ℕ → ℕ) (hf1 : 1 ≤ f 1)
    (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) (n : ℕ) (hn : 1 ≤ n) :
    let C : ℕ → ℕ := fun x => ((Finset.Icc 1 x).filter (fun m => f m ≤ x)).card
    nthNonValue f n = if f (C n + 1) ≤ n + C n then n + C n + 1 else n + C n

/-- Interleaving functions: let `f` satisfy the hypotheses of `nthNonValue_eq_one_step`, let
`α : ℕ → ℝ` interleave `f` (`f(m - 1) ≤ α(m) ≤ f(m)` for `m ≥ 2`), and let `h(n) ≥ 1` with
`α(h(n)) ≤ n < α(h(n) + 1)` (for increasing `α` with `α(1) = 1` this is the paper's
`h(n) = max {m ≥ 1 : α(m) ≤ n}`). Then `f_P(n)` is `n + h(n) + 1` if `n + h(n) ≥ f(h(n) + 1)`,
`n + h(n) - 1` if `n + h(n) ≤ f(h(n))`, and `n + h(n)` otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 3. -/
public theorem_wanted nthNonValue_eq_interleave (f : ℕ → ℕ) (hf1 : 1 ≤ f 1)
    (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) (α : ℕ → ℝ)
    (hα : ∀ m, 2 ≤ m → (f (m - 1) : ℝ) ≤ α m ∧ α m ≤ f m) (h : ℕ → ℕ)
    (hh : ∀ n, 1 ≤ n → 1 ≤ h n ∧ α (h n) ≤ n ∧ (n : ℝ) < α (h n + 1)) (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue f n =
      if f (h n + 1) ≤ n + h n then n + h n + 1
      else if n + h n ≤ f (h n) then n + h n - 1
      else n + h n

/-- Under the hypotheses of `nthNonValue_eq_interleave`, if moreover `f(m) - α(m) < m` for all
`m ≥ 1`, the middle case never occurs: `f_P(n) = n + h(n) + 1` if `n + h(n) ≥ f(h(n) + 1)` and
`f_P(n) = n + h(n)` otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 1. -/
public theorem_wanted nthNonValue_eq_interleave_of_sub_lt (f : ℕ → ℕ) (hf1 : 1 ≤ f 1)
    (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) (α : ℕ → ℝ)
    (hα : ∀ m, 2 ≤ m → (f (m - 1) : ℝ) ≤ α m ∧ α m ≤ f m) (h : ℕ → ℕ)
    (hh : ∀ n, 1 ≤ n → 1 ≤ h n ∧ α (h n) ≤ n ∧ (n : ℝ) < α (h n + 1))
    (hclose : ∀ m : ℕ, 1 ≤ m → (f m : ℝ) - α m < m) (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue f n = if f (h n + 1) ≤ n + h n then n + h n + 1 else n + h n

/-- Under the hypotheses of `nthNonValue_eq_interleave`, if moreover `f(m) - α(m) ≥ m` for all
`m > 1`, the first case never occurs: `f_P(n) = n + h(n)` if `n + h(n) > f(h(n))` and
`f_P(n) = n + h(n) - 1` otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 2. -/
public theorem_wanted nthNonValue_eq_interleave_of_le_sub (f : ℕ → ℕ) (hf1 : 1 ≤ f 1)
    (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) (α : ℕ → ℝ)
    (hα : ∀ m, 2 ≤ m → (f (m - 1) : ℝ) ≤ α m ∧ α m ≤ f m) (h : ℕ → ℕ)
    (hh : ∀ n, 1 ≤ n → 1 ≤ h n ∧ α (h n) ≤ n ∧ (n : ℝ) < α (h n + 1))
    (hfar : ∀ m : ℕ, 2 ≤ m → (m : ℝ) ≤ f m - α m) (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue f n = if f (h n) < n + h n then n + h n else n + h n - 1

/-- The `n`-th non-triangular number is `n + ⌊√(2n) + 1/2⌋`.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 3. -/
public theorem_wanted nthNonValue_triangular_eq_round (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue (fun j => j * (j + 1) / 2) n = n + ⌊Real.sqrt (2 * n) + 1 / 2⌋₊

/-- The `n`-th non-square number is `n + ⌊√n + 1/2⌋`.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 3. -/
public theorem_wanted nthNonValue_sq_eq_round (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue (fun j => j ^ 2) n = n + ⌊Real.sqrt n + 1 / 2⌋₊

/-- The `n`-th non-`k`-gonal number (`k ≥ 3`, `k`-gonal numbers
`T(k, j) = (k - 2) j (j - 1) / 2 + j`, `j ≥ 1`): with `s = ⌊√(2n / (k - 2))⌋`, it is `n + s + 1`
if `2n > (k - 2) s (s + 1)` and `n + s` otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 4, Equation (3). -/
public theorem_wanted nthNonValue_polygonal (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    let s := Nat.sqrt (2 * n / (k - 2))
    nthNonValue (fun j => (k - 2) * j * (j - 1) / 2 + j) n =
      if (k - 2) * s * (s + 1) < 2 * n then n + s + 1 else n + s

/-- For `3 ≤ k ≤ 10` the `n`-th non-`k`-gonal number is `n + ⌊√(2n / (k - 2)) + 1/2⌋`.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 4 (last sentence). -/
public theorem_wanted nthNonValue_polygonal_eq_round (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 10)
    (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue (fun j => (k - 2) * j * (j - 1) / 2 + j) n =
      n + ⌊Real.sqrt (2 * n / ((k : ℝ) - 2)) + 1 / 2⌋₊

/-- Shifted form: for `k ≥ 3` and real `r` with `-1 ≤ r ≤ k - 4`, with
`s = ⌊√((2n + r) / (k - 2))⌋`, the `n`-th non-`k`-gonal number is `n + s + 1` if
`2n > (k - 2) s (s + 1)` and `n + s` otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 5, Equation (4). -/
public theorem_wanted nthNonValue_polygonal_shift (k : ℕ) (hk : 3 ≤ k) (r : ℝ) (hr : -1 ≤ r)
    (hr' : r ≤ (k : ℝ) - 4) (n : ℕ) (hn : 1 ≤ n) :
    let s := ⌊Real.sqrt ((2 * n + r) / ((k : ℝ) - 2))⌋₊
    nthNonValue (fun j => (k - 2) * j * (j - 1) / 2 + j) n =
      if (k - 2) * s * (s + 1) < 2 * n then n + s + 1 else n + s

/-- For every `k ≥ 3` the `n`-th non-`k`-gonal number is
`n + ⌊√((2n - 2 + ⌊(k + 1)/4⌋) / (k - 2)) + 1/2⌋` (the choice `r = ⌊(k + 1)/4⌋ - 2`).

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 5 (last sentence). -/
public theorem_wanted nthNonValue_polygonal_eq_round_shift (k : ℕ) (hk : 3 ≤ k) (n : ℕ)
    (hn : 1 ≤ n) :
    nthNonValue (fun j => (k - 2) * j * (j - 1) / 2 + j) n =
      n + ⌊Real.sqrt ((2 * n - 2 + ((k + 1) / 4 : ℕ)) / ((k : ℝ) - 2)) + 1 / 2⌋₊

/-- The `n`-th non-second-pentagonal number (second pentagonal numbers `(3j² + j)/2`, `j ≥ 1`):
with `s = ⌊√(2n/3)⌋`, it is `n + s + 1` if `2n ≥ s(3s + 5) + 4` and `n + s` otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 6. -/
public theorem_wanted nthNonValue_secondPentagonal (n : ℕ) (hn : 1 ≤ n) :
    let s := Nat.sqrt (2 * n / 3)
    nthNonValue (fun j => (3 * j ^ 2 + j) / 2) n =
      if s * (3 * s + 5) + 4 ≤ 2 * n then n + s + 1 else n + s

/-- The `n`-th non-second-`k`-gonal number for `k > 5` (second `k`-gonal numbers
`((k - 2) j² + (k - 4) j)/2`, `j ≥ 1`): with `s = ⌊√(2n / (k - 2))⌋`, it is `n + s` if
`2n > (k - 2) s (s + 1) - 4s` and `n + s - 1` otherwise. The condition is written with `4s`
moved to the left side.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 7, Equation (5). -/
public theorem_wanted nthNonValue_secondPolygonal (k : ℕ) (hk : 5 < k) (n : ℕ) (hn : 1 ≤ n) :
    let s := Nat.sqrt (2 * n / (k - 2))
    nthNonValue (fun j => ((k - 2) * j ^ 2 + (k - 4) * j) / 2) n =
      if (k - 2) * s * (s + 1) < 2 * n + 4 * s then n + s else n + s - 1

/-- The `n`-th nonnegative non-centered-`k`-gonal number (`k ≥ 3`; centered `k`-gonal numbers
`k j (j + 1)/2 + 1`, `j ≥ 0`; the count starts at `0`, so the value at `n = 1` is `0`): with
`s = ⌊√(2n / k)⌋`, it is `n + s` if `2(n + s - 1) > k s (s + 1)` and `n + s - 1` otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 8. -/
public theorem_wanted nth_nonCenteredPolygonal (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    let s := Nat.sqrt (2 * n / k)
    Nat.nth (fun x => ∀ j, k * j * (j + 1) / 2 + 1 ≠ x) (n - 1) =
      if k * s * (s + 1) < 2 * (n + s - 1) then n + s else n + s - 1

/-- The `n`-th non-`k`-gonal-pyramidal number for `3 ≤ k ≤ 8` (pyramidal numbers
`j (j + 1)((k - 2) j - (k - 5))/6`, `j ≥ 1`): with `s = ⌊∛(6n / (k - 2))⌋`, it is `n + s + 1` if
`6n ≥ s³(k - 2) + 3s²(k - 1) + s(2k - 1) + 6`, `n + s - 1` if
`6n ≤ s(s - 1)(s(k - 2) + k + 1)`, and `n + s` otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 9, Equation (6). -/
public theorem_wanted nthNonValue_pyramidal (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8) (n : ℕ)
    (hn : 1 ≤ n) :
    let s := Nat.nthRoot 3 (6 * n / (k - 2))
    nthNonValue (fun j => j * (j + 1) * ((k - 2) * j + 5 - k) / 6) n =
      if s ^ 3 * (k - 2) + 3 * s ^ 2 * (k - 1) + s * (2 * k - 1) + 6 ≤ 6 * n then n + s + 1
      else if 6 * n ≤ s * (s - 1) * (s * (k - 2) + k + 1) then n + s - 1
      else n + s

/-- For `3 ≤ k ≤ 5` the `n`-th non-`k`-gonal-pyramidal number is, with `s = ⌊∛(6n / (k - 2))⌋`,
`n + s - 1` if `6n ≤ s(s - 1)(s(k - 2) + k + 1)` and `n + s` otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 4, Equation (7). -/
public theorem_wanted nthNonValue_pyramidal_two_case (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 5)
    (n : ℕ) (hn : 1 ≤ n) :
    let s := Nat.nthRoot 3 (6 * n / (k - 2))
    nthNonValue (fun j => j * (j + 1) * ((k - 2) * j + 5 - k) / 6) n =
      if 6 * n ≤ s * (s - 1) * (s * (k - 2) + k + 1) then n + s - 1 else n + s

/-- Equation (7) of Corollary 4 (the two-case formula of `nthNonValue_pyramidal_two_case`)
holds for all `3 ≤ k ≤ 8`, as the paper reports after checking small `n`.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, remark after Corollary 4. -/
public theorem_wanted nthNonValue_pyramidal_two_case_le_eight (k : ℕ) (hk : 3 ≤ k)
    (hk' : k ≤ 8) (n : ℕ) (hn : 1 ≤ n) :
    let s := Nat.nthRoot 3 (6 * n / (k - 2))
    nthNonValue (fun j => j * (j + 1) * ((k - 2) * j + 5 - k) / 6) n =
      if 6 * n ≤ s * (s - 1) * (s * (k - 2) + k + 1) then n + s - 1 else n + s

/-- The `n`-th non-sum-of-`k`-th-powers for `k > 1` (values `∑_{i=1}^j i^k`, `j ≥ 1`): with
`h = ⌊((k + 1) n)^{1/(k+1)}⌋`, it is `n + h - [n ≤ ∑_{i=1}^h (i^k - 1)]`.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 10 (third equivalent form). -/
public theorem_wanted nthNonValue_sumPow (k : ℕ) (hk : 1 < k) (n : ℕ) (hn : 1 ≤ n) :
    let h := Nat.nthRoot (k + 1) ((k + 1) * n)
    nthNonValue (fun j => ∑ i ∈ Finset.Icc 1 j, i ^ k) n =
      if n ≤ ∑ i ∈ Finset.Icc 1 h, (i ^ k - 1) then n + h - 1 else n + h

/-- The `n`-th positive integer not of the form `m + ∑_{i=1}^m i^k` (`m ≥ 1`, `k > 1`): with
`h = ⌊((k + 1) n)^{1/(k+1)}⌋`, it is `n + h - [n ≤ ∑_{i=1}^h i^k]`.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 11 (third equivalent form). -/
public theorem_wanted nthNonValue_add_sumPow (k : ℕ) (hk : 1 < k) (n : ℕ) (hn : 1 ≤ n) :
    let h := Nat.nthRoot (k + 1) ((k + 1) * n)
    nthNonValue (fun j => j + ∑ i ∈ Finset.Icc 1 j, i ^ k) n =
      if n ≤ ∑ i ∈ Finset.Icc 1 h, i ^ k then n + h - 1 else n + h

/-- The rising factorial `n^(k̄) = n (n + 1) ⋯ (n + k - 1)` satisfies
`(n + ⌊k/2⌋ - 1)^k ≤ n^(k̄) ≤ (n + ⌊k/2⌋)^k` for `n ≥ r`, where
`r = ⌊(k² - 4k + 6)/4⌋` for even `k` and `r = ⌊(k² - 6k + 11)/4⌋` for odd `k` (both numerators
are positive, written with the subtraction last).

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Lemma 1, Equation (8). -/
public theorem_wanted ascFactorial_bounds_half (k n : ℕ)
    (hn : (if Even k then (k ^ 2 + 6 - 4 * k) / 4 else (k ^ 2 + 11 - 6 * k) / 4) ≤ n) :
    (n + k / 2 - 1) ^ k ≤ n.ascFactorial k ∧ n.ascFactorial k ≤ (n + k / 2) ^ k

/-- The `n`-th non-`k`-simplex number for `1 < k ≤ 5`, `k = 7` or `k = 9` (simplex numbers
`binom(j + k - 1, k)`, `j ≥ 1`): with `R = ⌊(k! n)^{1/k}⌋` and `t = n + R - ⌊k/2⌋`, it is `t + 2`
if `t + 1 ≥ binom(R + ⌈k/2⌉ + 1, k)`, `t` if `t < binom(R + ⌈k/2⌉, k)`, and `t + 1` otherwise
(computed in `ℤ`).

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 12, Equation (9). -/
public theorem_wanted nthNonValue_simplex (k : ℕ) (hk : 1 < k ∧ k ≤ 5 ∨ k = 7 ∨ k = 9) (n : ℕ)
    (hn : 1 ≤ n) :
    let R := Nat.nthRoot k (k.factorial * n)
    let t : ℤ := n + R - (k / 2 : ℕ)
    (nthNonValue (fun j => (j + k - 1).choose k) n : ℤ) =
      if ((R + (k + 1) / 2 + 1).choose k : ℤ) ≤ t + 1 then t + 2
      else if t < ((R + (k + 1) / 2).choose k : ℤ) then t
      else t + 1

/-- Equation (9) of Theorem 12 (`nthNonValue_simplex`) holds for all `1 < k ≤ 15`.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 5. -/
public theorem_wanted nthNonValue_simplex_le_fifteen (k : ℕ) (hk : 1 < k) (hk' : k ≤ 15) (n : ℕ)
    (hn : 1 ≤ n) :
    let R := Nat.nthRoot k (k.factorial * n)
    let t : ℤ := n + R - (k / 2 : ℕ)
    (nthNonValue (fun j => (j + k - 1).choose k) n : ℤ) =
      if ((R + (k + 1) / 2 + 1).choose k : ℤ) ≤ t + 1 then t + 2
      else if t < ((R + (k + 1) / 2).choose k : ℤ) then t
      else t + 1

end

end MetaMathlibExt
