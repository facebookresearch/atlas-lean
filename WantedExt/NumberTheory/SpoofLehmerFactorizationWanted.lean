/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Card

/-!
# Spoof Lehmer factorizations (wanted statements)

Statements from Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26
(2026), Article A33. A spoof factorization `x_1^{a_1} ⋯ x_r^{a_r}` is a multiset of pairs
`(x_i, a_i)` of positive integers; `x_1 ⋯ x_r` denotes the factorization with all exponents `1`,
encoded as `Multiset.map (fun a => (a, 1)) x`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- A spoof factorization: a finite multiset of pairs `(base, exponent)` of positive integers.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 1. -/
def IsSpoofFactorization (F : Multiset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ F, 0 < p.1 ∧ 0 < p.2

/-- The spoof evaluation `ẽ(x_1^{a_1} ⋯ x_r^{a_r}) = ∏ x_i^{a_i}`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 2. -/
def spoofEval (F : Multiset (ℕ × ℕ)) : ℤ :=
  (F.map fun p => (p.1 : ℤ) ^ p.2).prod

/-- The spoof totient `φ̃(x_1^{a_1} ⋯ x_r^{a_r}) = ∏ (x_i^{a_i} - x_i^{a_i - 1})`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 3. -/
def spoofTotient (F : Multiset (ℕ × ℕ)) : ℤ :=
  (F.map fun p => (p.1 : ℤ) ^ p.2 - (p.1 : ℤ) ^ (p.2 - 1)).prod

/-- Characteristic values: `ẽ(3 ⋅ 3) = 9` and `φ̃(3 ⋅ 3) = 4`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definitions 2 and 3. -/
theorem spoofEval_spoofTotient_three_three :
    spoofEval {(3, 1), (3, 1)} = 9 ∧ spoofTotient {(3, 1), (3, 1)} = 4 := by
  norm_num [spoofEval, spoofTotient]

/-- `F` is a (spoof) `k`-Lehmer factorization: `F` is a spoof factorization (positive bases and
exponents), `k ⋅ φ̃(F) = ẽ(F) - 1`, and `F` has at least two factors or a factor with exponent
greater than `1`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 4. -/
def IsSpoofLehmer (k : ℤ) (F : Multiset (ℕ × ℕ)) : Prop :=
  IsSpoofFactorization F ∧ k * spoofTotient F = spoofEval F - 1 ∧
    (2 ≤ Multiset.card F ∨ ∃ p ∈ F, 1 < p.2)

/-- Characteristic example: `3 ⋅ 3` is a `2`-Lehmer factorization.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Table 1. -/
theorem isSpoofLehmer_three_three : IsSpoofLehmer 2 {(3, 1), (3, 1)} :=
  ⟨by simp [IsSpoofFactorization], by norm_num [spoofEval, spoofTotient], Or.inl (by simp)⟩

/-- Characteristic example: `1^a ⋅ 1^b` (`a, b > 0`) is a `k`-Lehmer factorization for every `k`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Example 1. -/
theorem isSpoofLehmer_one_one (k : ℤ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    IsSpoofLehmer k {(1, a), (1, b)} :=
  ⟨by simp [IsSpoofFactorization, ha, hb], by simp [spoofEval, spoofTotient], Or.inl (by simp)⟩

/-- A spoof factorization is trivial if every base is `1`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 6. -/
def IsTrivialSpoof (F : Multiset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ F, p.1 = 1

/-- A spoof factorization is odd if every base is odd (and even otherwise).

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 7. -/
def IsOddSpoof (F : Multiset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ F, Odd p.1

/-- The spoof factorization `x_1 ⋯ x_r = x_1^1 ⋯ x_r^1` on the bases `x`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Remark 3. -/
def spoofOfBases (x : Multiset ℕ) : Multiset (ℕ × ℕ) :=
  x.map fun a => (a, 1)

/-- Characteristic value: the bases `3, 3` give the factorization `3 ⋅ 3 = 3^1 ⋅ 3^1`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Remark 3. -/
theorem spoofOfBases_three_three : spoofOfBases {3, 3} = {(3, 1), (3, 1)} := by
  simp [spoofOfBases]

/-- `x` (a multiset of integers `x_j ≥ 2`) solves Equation (1),
`k ∏ (x_j - 1) = ∏ x_j - 1`, for some `k ∈ ℤ_{>0}`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Equation (1). -/
def IsLehmerEquationSolution (x : Multiset ℕ) : Prop :=
  (∀ a ∈ x, 2 ≤ a) ∧ ∃ k : ℤ, 0 < k ∧
    k * (x.map fun a : ℕ => (a : ℤ) - 1).prod = (x.map fun a : ℕ => (a : ℤ)).prod - 1

/-- Characteristic example: `x = (3, 3)` solves Equation (1) with `k = 2`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Table 1. -/
theorem isLehmerEquationSolution_three_three : IsLehmerEquationSolution {3, 3} :=
  ⟨by simp, 2, by norm_num, by norm_num⟩

/-- The function `κ_r(t_1, …, t_r) = (t_1 ⋯ t_r - 1) / ((t_1 - 1) ⋯ (t_r - 1))`, on lists of
length `r`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 8. -/
noncomputable def lehmerKappa (t : List ℝ) : ℝ :=
  (t.prod - 1) / (t.map (· - 1)).prod

/-- Characteristic value: `κ_2(2, 2) = 3`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 8 and proof of Theorem 5. -/
theorem lehmerKappa_two_two : lehmerKappa [2, 2] = 3 := by
  simp only [lehmerKappa, List.prod_cons, List.prod_nil, List.map_cons, List.map_nil]
  norm_num

/-- The admissible completions `u_{s+1} ≤ ⋯ ≤ u_r` of `t_1 ≤ ⋯ ≤ t_s` used in Definition 9:
lists `u` with `s + |u| = r`, `t ⌢ u` nondecreasing and every `u_j ≥ 2`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9. -/
def lehmerCompletions (t : List ℝ) (r : ℕ) : Set (List ℝ) :=
  {u | t.length + u.length = r ∧ (t ++ u).Pairwise (· ≤ ·) ∧ ∀ x ∈ u, 2 ≤ x}

/-- `L(t_1, …, t_s; r)`: the infimum of `κ_r(t_1, …, t_s, u_{s+1}, …, u_r)` over admissible
completions.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9. -/
noncomputable def lehmerLower (t : List ℝ) (r : ℕ) : ℝ :=
  sInf ((fun u => lehmerKappa (t ++ u)) '' lehmerCompletions t r)

/-- `U(t_1, …, t_s; r)`: the supremum of `κ_r(t_1, …, t_s, u_{s+1}, …, u_r)` over admissible
completions.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9. -/
noncomputable def lehmerUpper (t : List ℝ) (r : ℕ) : ℝ :=
  sSup ((fun u => lehmerKappa (t ++ u)) '' lehmerCompletions t r)

/-- Characteristic property: a nondecreasing list of length `r` has only the empty completion.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9. -/
theorem lehmerCompletions_length {t : List ℝ} (ht : t.Pairwise (· ≤ ·)) :
    lehmerCompletions t t.length = {[]} := by
  ext u
  simp only [lehmerCompletions, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, -, -⟩
    exact List.eq_nil_of_length_eq_zero (by omega)
  · rintro rfl
    simpa using ht

/-- Characteristic value: for `s = r`, `L(t; r) = U(t; r) = κ_r(t)`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9 and proof of Lemma 3. -/
theorem lehmerLower_upper_length {t : List ℝ} (ht : t.Pairwise (· ≤ ·)) :
    lehmerLower t t.length = lehmerKappa t ∧ lehmerUpper t t.length = lehmerKappa t := by
  simp [lehmerLower, lehmerUpper, lehmerCompletions_length ht]

/-- A Lehmer factorization having `1` as a base is trivial.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Proposition 1 (`integers-2026-A33-prop-1`). -/
public theorem_wanted isTrivialSpoof_of_isSpoofLehmer_of_one_mem (F : Multiset (ℕ × ℕ))
    (hL : ∃ k : ℤ, IsSpoofLehmer k F) (h1 : ∃ p ∈ F, p.1 = 1) :
    IsTrivialSpoof F

/-- Every exponent of a nontrivial spoof Lehmer factorization is `1`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 3 (`integers-2026-A33-thm-3`). -/
public theorem_wanted spoofLehmer_exponents_eq_one (F : Multiset (ℕ × ℕ))
    (k : ℤ) (hL : IsSpoofLehmer k F) (hnt : ¬ IsTrivialSpoof F) : ∀ p ∈ F, p.2 = 1

/-- Let `F = x_1 ⋯ x_r` be a nontrivial spoof Lehmer factorization. For any integer `n` dividing
`ẽ(F)` and any base `x_i`, `x_i ≢ 1 (mod n)`. Corrected reading: `n` is a non-unit (`n ≠ ±1`).
As printed the claim fails for `n = 1`: `3 ⋅ 3` is `2`-Lehmer (`2 ⋅ 4 = 9 - 1`) and
`3 ≡ 1 (mod 1)`; the proof's contradiction `0 ≡ -1 (mod n)` needs `n ∤ 1`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 4 (`integers-2026-A33-thm-4`). -/
public theorem_wanted spoofLehmer_base_not_modEq_one (x : Multiset ℕ) (k : ℤ)
    (hL : IsSpoofLehmer k (spoofOfBases x))
    (hnt : ¬ IsTrivialSpoof (spoofOfBases x)) (n : ℤ)
    (hn : n ∣ spoofEval (spoofOfBases x)) (hunit : ¬ IsUnit n) :
    ∀ a ∈ x, ¬ (a : ℤ) ≡ 1 [ZMOD n]

/-- If `F = x_1 ⋯ x_r` is a nontrivial spoof Lehmer factorization, then `x_i ≢ 1 (mod x_j)` for
all `i, j` (the record's range `1 ≤ i, j ≤ n` is the paper's typo for `r`).

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Corollary 1 (`integers-2026-A33-cor-1`). -/
public theorem_wanted spoofLehmer_base_not_modEq_one_base (x : Multiset ℕ) (k : ℤ)
    (hL : IsSpoofLehmer k (spoofOfBases x))
    (hnt : ¬ IsTrivialSpoof (spoofOfBases x)) :
    ∀ a ∈ x, ∀ b ∈ x, ¬ a ≡ 1 [MOD b]

/-- If `F = x_1 ⋯ x_r` is a nontrivial spoof Lehmer factorization and `p` is a prime dividing
`ẽ(F)`, then no base is `≡ 1 (mod p)`; in particular, if `F` is even then all its bases are even.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Corollary 2 (`integers-2026-A33-cor-2`). -/
public theorem_wanted spoofLehmer_base_not_modEq_one_prime (x : Multiset ℕ) (k : ℤ)
    (hL : IsSpoofLehmer k (spoofOfBases x))
    (hnt : ¬ IsTrivialSpoof (spoofOfBases x)) :
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ spoofEval (spoofOfBases x) →
      ∀ a ∈ x, ¬ a ≡ 1 [MOD p]) ∧
    (¬ IsOddSpoof (spoofOfBases x) → ∀ a ∈ x, Even a)

/-- `κ_r` is strictly decreasing in each argument on `[2, ∞)^r` and `1 < κ_r ≤ 2^r - 1` there.
Corrected domain `r ≥ 2`: for `r = 1`, `κ_1 ≡ 1`, so `1 < κ_1(2)` fails and `κ_1` is constant;
the paper's derivative argument uses `κ_{r-1} > 0`, true only for `r ≥ 2`. Points are lists of
length `r`; "decreasing in the `j`-th argument" is stated with `List.set`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 5 (`integers-2026-A33-thm-5`). -/
public theorem_wanted lehmerKappa_antitone_bounds (r : ℕ) (hr : 2 ≤ r) (t : List ℝ)
    (hlen : t.length = r)
    (ht : ∀ x ∈ t, 2 ≤ x) :
    (1 < lehmerKappa t ∧ lehmerKappa t ≤ 2 ^ r - 1) ∧
      ∀ (j : ℕ) (hj : j < t.length) (y : ℝ), t[j] < y → lehmerKappa (t.set j y) < lehmerKappa t

/-- `L(∅; r) = 1`, `U(∅; r) = 2^r - 1`, and for `2 ≤ t_1 ≤ ⋯ ≤ t_s` with `s > 0`:
`L(t; r) = t_1 ⋯ t_s / ((t_1 - 1) ⋯ (t_s - 1))` and
`U(t; r) = (t_1 ⋯ t_{s-1} t_s^{r-s+1} - 1) / ((t_1 - 1) ⋯ (t_{s-1} - 1)(t_s - 1)^{r-s+1})`.
Corrected domains: the `L` formulas need `r > s` (`r ≥ 1` for `L(∅; r)`), as the proof's
`L = lim_{u → ∞} κ(t, u, …, u)` requires a free argument. At `s = r` the infimum is over the
single completion, so `L(t; r) = κ_r(t)`: for `t = (2)`, `r = 1`, `L = κ_1(2) = 1` while the
formula gives `2`; and `L(∅; 0) = κ_0 = 0`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Lemma 1 (`integers-2026-A33-lem-1`). -/
public theorem_wanted lehmerLower_upper_formula :
    (∀ r : ℕ, 1 ≤ r → lehmerLower [] r = 1) ∧ (∀ r : ℕ, lehmerUpper [] r = 2 ^ r - 1) ∧
    ∀ (t : List ℝ) (r : ℕ) (hne : t ≠ []), t.Pairwise (· ≤ ·) → (∀ x ∈ t, 2 ≤ x) →
      t.length ≤ r →
      (t.length < r → lehmerLower t r = t.prod / (t.map (· - 1)).prod) ∧
      lehmerUpper t r = (t.dropLast.prod * t.getLast hne ^ (r - t.length + 1) - 1) /
        ((t.dropLast.map (· - 1)).prod * (t.getLast hne - 1) ^ (r - t.length + 1))

/-- For `0 ≤ s ≤ r`, `L(t_1, …, t_s; r)` and `U(t_1, …, t_s; r)` are monotonically decreasing in
`t_1, …, t_s` (on nondecreasing tuples with `t_1 ≥ 2`), stated as: increasing the arguments
pointwise does not increase `L` or `U`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Lemma 2 (`integers-2026-A33-lem-2`). -/
public theorem_wanted lehmerLower_upper_antitone (r : ℕ) (t t' : List ℝ) (hs : t.length ≤ r)
    (ht : t.Pairwise (· ≤ ·)) (ht' : t'.Pairwise (· ≤ ·)) (h2 : ∀ x ∈ t, 2 ≤ x)
    (hle : List.Forall₂ (· ≤ ·) t t') :
    lehmerLower t' r ≤ lehmerLower t r ∧ lehmerUpper t' r ≤ lehmerUpper t r

/-- Let `F = x_1 ⋯ x_r` (`x_1 ≤ ⋯ ≤ x_r`) be a nontrivial spoof `k`-Lehmer factorization. For
every partial factorization `G = x_1 ⋯ x_s` (`0 ≤ s ≤ r`), `L(G; r) ≤ k ≤ U(G; r)`, with
equality on the left iff `G = F` (i.e. `s = r`); in particular `1 < k ≤ 2^r - 1`. Exponents `1`
as in Definition 11 (justified by Theorem 3).

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Lemma 3 (`integers-2026-A33-lem-3`). -/
public theorem_wanted spoofLehmer_lower_le_le_upper (x : List ℕ) (hsorted : x.Pairwise (· ≤ ·))
    (k : ℤ) (hL : IsSpoofLehmer k (spoofOfBases x))
    (hnt : ¬ IsTrivialSpoof (spoofOfBases x)) :
    (∀ s ≤ x.length,
      lehmerLower ((x.take s).map (fun a : ℕ => (a : ℝ))) x.length ≤ k ∧
      (k : ℝ) ≤ lehmerUpper ((x.take s).map (fun a : ℕ => (a : ℝ))) x.length ∧
      (lehmerLower ((x.take s).map (fun a : ℕ => (a : ℝ))) x.length = k ↔ s = x.length)) ∧
    1 < k ∧ k ≤ 2 ^ x.length - 1

/-- For every `r ≥ 2`, Equation (1), `k ∏ (x_j - 1) = ∏ x_j - 1` with `k ∈ ℤ_{>0}`, has only
finitely many solutions with `x_1, …, x_r ≥ 2`. Omitted: the meta-claim that the solutions can
be explicitly computed.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 1 (`integers-2026-A33-thm-1`). -/
public theorem_wanted lehmerEquation_solutions_finite (r : ℕ) (hr : 2 ≤ r) :
    {p : ℤ × (Fin r → ℕ) | 0 < p.1 ∧ (∀ i, 2 ≤ p.2 i) ∧
      p.1 * ∏ i, ((p.2 i : ℤ) - 1) = ∏ i, (p.2 i : ℤ) - 1}.Finite

/-- For `2 ≤ r ≤ 6`, Equation (1) has `76` solutions with all `x_i ≥ 2`: `31` with all `x_i` odd
(`≥ 3`) and `45` with all `x_i` even. Solutions are counted up to order of the `x_i` (multisets,
as in Tables 1 and 2).

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 2 (`integers-2026-A33-thm-2`). -/
public theorem_wanted lehmerEquation_solutions_count :
    Set.ncard {x : Multiset ℕ | 2 ≤ Multiset.card x ∧ Multiset.card x ≤ 6 ∧
      IsLehmerEquationSolution x} = 76 ∧
    Set.ncard {x : Multiset ℕ | 2 ≤ Multiset.card x ∧ Multiset.card x ≤ 6 ∧
      IsLehmerEquationSolution x ∧ ∀ a ∈ x, Odd a} = 31 ∧
    Set.ncard {x : Multiset ℕ | 2 ≤ Multiset.card x ∧ Multiset.card x ≤ 6 ∧
      IsLehmerEquationSolution x ∧ ∀ a ∈ x, Even a} = 45

/-- For every `r`, there are only finitely many nontrivial (spoof) Lehmer factorizations with
`r` factors. Omitted: the meta-claim that they can be explicitly and verifiably computed.
Domain extension: also for `r = 0` (no Lehmer factorization has no factors).

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 6 (`integers-2026-A33-thm-6`). -/
public theorem_wanted spoofLehmer_finite (r : ℕ) :
    {F : Multiset (ℕ × ℕ) | Multiset.card F = r ∧
      (∃ k : ℤ, IsSpoofLehmer k F) ∧ ¬ IsTrivialSpoof F}.Finite

/-- The nontrivial odd spoof Lehmer factorizations with at most `6` factors are exactly the `31`
listed in Table 1, and the nontrivial even ones are exactly the `45` listed in Table 2 (all
exponents `1`). Omitted: the attribution of `11` odd and `27` even ones to the families of
Examples 2–5 and the resulting counts `20` and `18` of sporadic ones (the record text is
truncated after "Example 2,"; the lists follow Tables 1 and 2 of the paper).

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 7 (`integers-2026-A33-thm-7`). -/
public theorem_wanted spoofLehmer_atMostSix_tables :
    {F : Multiset (ℕ × ℕ) | Multiset.card F ≤ 6 ∧
      (∃ k : ℤ, IsSpoofLehmer k F) ∧ ¬ IsTrivialSpoof F ∧ IsOddSpoof F} =
      {F | ∃ l ∈ ([
      [3, 3], [3, 5, 15], [3, 5, 17, 255], [3, 3, 3, 3], [3, 5, 17, 257, 65535],
      [3, 5, 17, 285, 2507], [5, 5, 5, 43, 5375], [5, 5, 9, 9, 89],
      [3, 5, 17, 257, 65537, 4294967295], [3, 5, 17, 257, 65555, 226112997],
      [3, 5, 17, 257, 65717, 23794275], [3, 5, 17, 257, 68975, 1314417],
      [3, 5, 17, 353, 929, 83623935], [3, 5, 17, 377, 1217, 2295], [3, 5, 17, 395, 1059, 2303],
      [3, 5, 33, 53, 69, 8343], [3, 9, 9, 23, 131, 732159], [5, 5, 5, 43, 5377, 28901375],
      [5, 5, 5, 43, 5387, 2632285], [5, 5, 5, 43, 5407, 937505], [5, 5, 5, 43, 5477, 291475],
      [5, 5, 5, 43, 5717, 90115], [5, 5, 5, 43, 6215, 39817], [5, 5, 5, 43, 6487, 31385],
      [5, 5, 5, 43, 8507, 14605], [5, 5, 5, 45, 807, 267023], [5, 5, 5, 47, 453, 2661375],
      [5, 5, 5, 47, 457, 50659], [5, 5, 5, 65, 129, 2325], [5, 7, 7, 7, 133, 228095],
      [3, 3, 5, 5, 9, 89]] : List (List ℕ)),
        F = spoofOfBases (l : Multiset ℕ)} ∧
    {F : Multiset (ℕ × ℕ) | Multiset.card F ≤ 6 ∧
      (∃ k : ℤ, IsSpoofLehmer k F) ∧ ¬ IsTrivialSpoof F ∧ ¬ IsOddSpoof F} =
      {F | ∃ l ∈ ([
      [2, 2], [2, 4, 8], [2, 2, 4], [2, 2, 2], [2, 4, 10, 80], [2, 2, 6, 24], [2, 2, 4, 4],
      [2, 2, 2, 8], [2, 2, 2, 2], [2, 4, 10, 82, 6560], [2, 4, 10, 92, 670], [2, 4, 10, 100, 422],
      [2, 4, 10, 112, 290], [2, 2, 6, 26, 624], [2, 2, 8, 12, 384], [2, 2, 2, 10, 80],
      [2, 2, 2, 4, 32], [2, 2, 2, 2, 16], [2, 2, 2, 2, 6], [2, 2, 2, 2, 4], [2, 2, 2, 2, 2],
      [2, 4, 10, 82, 6562, 43046720], [2, 4, 10, 82, 12440, 13882], [2, 4, 10, 88, 1120, 9944],
      [2, 4, 26, 26, 26, 8272], [2, 8, 8, 8, 206, 210944], [2, 2, 6, 26, 626, 390624],
      [2, 2, 6, 42, 62, 2156], [2, 2, 8, 12, 386, 148224], [2, 2, 8, 12, 404, 8166],
      [2, 2, 8, 12, 416, 5154], [2, 2, 8, 12, 636, 974], [2, 2, 12, 14, 18, 206],
      [2, 2, 2, 10, 82, 6560], [2, 2, 2, 10, 92, 670], [2, 2, 2, 10, 100, 422],
      [2, 2, 2, 10, 112, 290], [2, 2, 2, 4, 34, 1088], [2, 2, 2, 4, 38, 244], [2, 2, 2, 6, 8, 384],
      [2, 2, 2, 4, 8, 16], [2, 2, 2, 2, 18, 288], [2, 2, 2, 2, 6, 6], [2, 2, 2, 2, 2, 32],
      [2, 2, 2, 2, 2, 2]] : List (List ℕ)),
        F = spoofOfBases (l : Multiset ℕ)}

end

end MetaMathlibExt
