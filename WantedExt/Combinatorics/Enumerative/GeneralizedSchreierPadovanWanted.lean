/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Real.Basic

/-!
# Generalized Schreier sets and Padovan-like sequences

Statements from Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized
Schreier Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2. For positive
integers `p, q`, a finite nonempty set `F` of positive integers is `(p, q)`-Schreier if
`q min F ≥ p |F|` and maximal `(p, q)`-Schreier if `q min F = p |F|`; `S^{p/q}_n` and
`M^{p/q}_n` collect those with `max F = n`. Their counts are taken `q`-periodically from the
Padovan-like sequences `a_{p,q,n}` and `a^{(m)}_{p,q,n}`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- `|S^{p/q}_n|`, the number of `(p, q)`-Schreier sets with maximum `n`: subsets
`F ⊆ {1, …, n}` with `n ∈ F` and `p |F| ≤ q x` for all `x ∈ F` (that is, `q min F ≥ p |F|`).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
def schreierCount (p q n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun F => n ∈ F ∧ ∀ x ∈ F, p * F.card ≤ q * x).card

/-- `|M^{p/q}_n|`, the number of maximal `(p, q)`-Schreier sets with maximum `n`: subsets
`F ⊆ {1, …, n}` with `n ∈ F` and `q min F = p |F|`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
def maximalSchreierCount (p q n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun F =>
    n ∈ F ∧ (∀ x ∈ F, p * F.card ≤ q * x) ∧ ∃ x ∈ F, q * x = p * F.card).card

/-- The Padovan-like sequence `a_{p,q,n}`: for `p ≥ q`, `a_n = 0` for `n < p - q` and `a_n = 1`
for `p - q ≤ n < p + q`; for `p < q`, `a_n = 1` for `n < 2p` and `a_n = 2` for
`2p ≤ n < p + q`; and `a_n = a_{n-q} + a_{n-p-q}` for `n ≥ p + q` (when `q ≥ 1`).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
def schreierPadovan (p q : ℕ) : ℕ → ℕ
  | n =>
    if _h : p + q ≤ n ∧ 0 < q then
      schreierPadovan p q (n - q) + schreierPadovan p q (n - p - q)
    else if q ≤ p then (if n + q < p then 0 else 1) else (if n < 2 * p then 1 else 2)
  decreasing_by all_goals omega

/-- The Padovan-like sequence `a^{(m)}_{p,q,n}` for maximal Schreier sets: for `p ≥ q`, the
initial values `a_n`, `n < p + q`, are `1` at `n = p - q` and `0` otherwise; for `p < q`, they
are `1` at `n = 2p` and `0` otherwise; and `a_n = a_{n-q} + a_{n-p-q}` for `n ≥ p + q`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
def maximalSchreierPadovan (p q : ℕ) : ℕ → ℕ
  | n =>
    if _h : p + q ≤ n ∧ 0 < q then
      maximalSchreierPadovan p q (n - q) + maximalSchreierPadovan p q (n - p - q)
    else if q ≤ p then (if n + q = p then 1 else 0) else (if n = 2 * p then 1 else 0)
  decreasing_by all_goals omega

/-- The recurrence `a_{p,q,n} = a_{p,q,n-q} + a_{p,q,n-p-q}` for `n ≥ p + q`, `q ≥ 1`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
theorem schreierPadovan_rec {p q n : ℕ} (hq : 0 < q) (hn : p + q ≤ n) :
    schreierPadovan p q n = schreierPadovan p q (n - q) + schreierPadovan p q (n - p - q) := by
  rw [schreierPadovan]
  simp only [hn, hq, and_self, ↓reduceDIte]

/-- The recurrence `a^{(m)}_{p,q,n} = a^{(m)}_{p,q,n-q} + a^{(m)}_{p,q,n-p-q}` for
`n ≥ p + q`, `q ≥ 1`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
theorem maximalSchreierPadovan_rec {p q n : ℕ} (hq : 0 < q) (hn : p + q ≤ n) :
    maximalSchreierPadovan p q n =
      maximalSchreierPadovan p q (n - q) + maximalSchreierPadovan p q (n - p - q) := by
  rw [maximalSchreierPadovan]
  simp only [hn, hq, and_self, ↓reduceDIte]

/-- Table 3 values: `a_{1,2,n} = 1, 1, 2, 2, 3, 4, 5, 7` and `a_{2,1,n} = 0, 1, 1, 1, 2, 3, 4, 6`
for `n = 0, …, 7`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Table 3. -/
theorem schreierPadovan_small :
    (List.range 8).map (schreierPadovan 1 2) = [1, 1, 2, 2, 3, 4, 5, 7] ∧
      (List.range 8).map (schreierPadovan 2 1) = [0, 1, 1, 1, 2, 3, 4, 6] := by
  decide +kernel

/-- Table 4 values: `a^{(m)}_{1,2,n} = 0, 0, 1, 0, 1, 1, 1, 2` and
`a^{(m)}_{2,1,n} = 0, 1, 0, 0, 1, 1, 1, 2` for `n = 0, …, 7`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Table 4. -/
theorem maximalSchreierPadovan_small :
    (List.range 8).map (maximalSchreierPadovan 1 2) = [0, 0, 1, 0, 1, 1, 1, 2] ∧
      (List.range 8).map (maximalSchreierPadovan 2 1) = [0, 1, 0, 0, 1, 1, 1, 2] := by
  decide +kernel

/-- Table 1 and 2 values: `|S^{1/2}_n| = 1, 2, 3, 5` and `|M^{1/2}_n| = 0, 1, 1, 1` for
`n = 1, …, 4`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Tables 1 and 2. -/
theorem schreierCount_one_two_small :
    (List.range 4).map (fun n => schreierCount 1 2 (n + 1)) = [1, 2, 3, 5] ∧
      (List.range 4).map (fun n => maximalSchreierCount 1 2 (n + 1)) = [0, 1, 1, 1] := by
  decide +kernel

/-- A sequence `(a_n)` satisfies the polynomial `P = c_0 + c_1 x + ⋯ + c_r x^r` (with
`r = natDegree P`) if `c_0 a_n + c_1 a_{n-1} + ⋯ + c_r a_{n-r} = 0` for all `n ≥ r`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 4, Definition 4. -/
def SatisfiesPoly (P : Polynomial ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ n, P.natDegree ≤ n → ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * a (n - i) = 0

/-- Every sequence satisfies the zero polynomial.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 4, Definition 4. -/
theorem satisfiesPoly_zero (a : ℕ → ℝ) : SatisfiesPoly 0 a := by
  intro n _
  simp

/-- **Theorem 1.** For positive integers `p, q, n`, `|S^{p/q}_n| = a_{p,q,(n-1)q}` and
`|M^{p/q}_n| = a^{(m)}_{p,q,(n-1)q}`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Theorem 1
(`jis-2026-26.2.2-thm-1`). -/
public theorem_wanted schreierCount_eq_schreierPadovan {p q n : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hn : 1 ≤ n) :
    schreierCount p q n = schreierPadovan p q ((n - 1) * q) ∧
      maximalSchreierCount p q n = maximalSchreierPadovan p q ((n - 1) * q)

/-- **Corollary 2.** `|S^{p/q}_n| = ∑_{i=1}^{⌊(n+1)q/(p+q)⌋} C(n - ⌈pi/q⌉, i - 1)`, and
`|S^{p/q}_n| = ∑_{i=1}^q (-1)^{i+1} C(q, i) |S^{p/q}_{n-i}| + |S^{p/q}_{n-(p+q)}|` for
`n ≥ p + q + 1`.

The printed initial-term formula has `⌈ni/q⌉`, which is false (`p = 1`, `q = 2`, `n = 2`:
`|S^{1/2}_2| = 2` but the printed sum is `1`); `⌈pi/q⌉` is the paper's own formula (Section 3,
equation for `|S^{p/q}_n|`). That formula holds for every `n` (the corollary states it for
`1 ≤ n ≤ p + q`), so the range restriction is dropped; on its range `n - ⌈pi/q⌉ ≥ i - 1`, so the
natural-number subtraction is exact.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Corollary 2
(`jis-2026-26.2.2-cor-2`). -/
public theorem_wanted schreierCount_formula_and_recurrence {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (∀ n, schreierCount p q n =
      ∑ i ∈ Finset.Icc 1 ((n + 1) * q / (p + q)), (n - (p * i + q - 1) / q).choose (i - 1)) ∧
    ∀ n, p + q + 1 ≤ n →
      (schreierCount p q n : ℤ) =
        ∑ i ∈ Finset.Icc 1 q, (-1) ^ (i + 1) * (q.choose i : ℤ) * schreierCount p q (n - i) +
          schreierCount p q (n - (p + q))

/-- **Corollary 3.** With `p' = p / gcd(p, q)` and `q' = q / gcd(p, q)`,
`|M^{p/q}_n| = ∑_{k=1}^{⌊(n+1)/(p'+q')⌋} C(n - p'k - 1, q'k - 2)`, and
`|M^{p/q}_n| = ∑_{i=1}^q (-1)^{i+1} C(q, i) |M^{p/q}_{n-i}| + |M^{p/q}_{n-(p+q)}|` for
`n ≥ p + q + 1`.

The initial-term formula is corrected: the terms with `q'k - 2 < 0` (only `q' = k = 1`) are `0`,
and the singleton `{n}`, which is maximal exactly when `q' = 1` and `n = p'`, is added as a
separate `1`, as in the paper's proof of Theorem 1 (equation (10)). As printed (with binomials
vanishing at negative lower index) the formula misses it: `p = q = n = 1` gives `|M^{1/1}_1| = 1`
but the printed sum is `0`. The formula holds for every `n`, so the range `1 ≤ n ≤ p + q` is
dropped.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Corollary 3
(`jis-2026-26.2.2-cor-3`). -/
public theorem_wanted maximalSchreierCount_formula_and_recurrence {p q : ℕ} (hp : 1 ≤ p)
    (hq : 1 ≤ q) :
    (∀ n, maximalSchreierCount p q n =
      ∑ k ∈ (Finset.Icc 1 ((n + 1) / (p / p.gcd q + q / p.gcd q))).filter
          (fun k => 2 ≤ q / p.gcd q * k),
        (n - p / p.gcd q * k - 1).choose (q / p.gcd q * k - 2) +
      if q / p.gcd q = 1 ∧ n = p / p.gcd q then 1 else 0) ∧
    ∀ n, p + q + 1 ≤ n →
      (maximalSchreierCount p q n : ℤ) =
        ∑ i ∈ Finset.Icc 1 q,
            (-1) ^ (i + 1) * (q.choose i : ℤ) * maximalSchreierCount p q (n - i) +
          maximalSchreierCount p q (n - (p + q))

/-- **Lemma 5.** If a sequence satisfies `P` and `P ∣ Q`, then it satisfies `Q`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Lemma 5
(`jis-2026-26.2.2-lem-5`). -/
public theorem_wanted SatisfiesPoly.of_dvd {P Q : Polynomial ℝ} {a : ℕ → ℝ}
    (h : SatisfiesPoly P a) (hPQ : P ∣ Q) : SatisfiesPoly Q a

/-- **Theorem 8.** For `p ≥ 1`, `|S^{p/1}_n| = |M^{p/1}_{n+p+1}|`. The paper states it for
`n ≥ 1`; it also holds at `n = 0` (both sides are `0`).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Theorem 8
(`jis-2026-26.2.2-thm-8`). -/
public theorem_wanted schreierCount_eq_maximalSchreierCount_add {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    schreierCount p 1 n = maximalSchreierCount p 1 (n + p + 1)

/-- **Theorem 9.** For positive integers `q, n`, `|M^{1/q}_n| = 2|S^{1/q}_n| - |S^{1/q}_{n+1}|`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Theorem 9
(`jis-2026-26.2.2-thm-9`). -/
public theorem_wanted maximalSchreierCount_eq_two_mul_sub {q n : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) :
    (maximalSchreierCount 1 q n : ℤ) = 2 * schreierCount 1 q n - schreierCount 1 q (n + 1)

end

end MetaMathlibExt
