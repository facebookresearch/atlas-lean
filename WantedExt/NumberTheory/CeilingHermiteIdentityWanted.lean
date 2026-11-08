/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.BigOperators
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Inclusion-exclusion-like sums with floor, ceiling and nearest-integer functions (statements)

Mathlib proves Hermite's identity for the floor function as `Int.sum_floor_add_div`
(`∑_{0 ≤ i < n} ⌊x + i/n⌋ = ⌊n x⌋`). This file states the ceiling analogue with the shifted
range `1 ≤ k ≤ n` used by Onphaeng, Khemaratchatakumthorn and Pongsriiam, and the paper's sharp
bounds for the sums `g^(F)`, `f^(F)` and the partial sums `S^(F)`, `T^(F)` of Jacobsthal and
Tverberg type, where `F` is one of `⌊·⌋` (`j = 1`), `⌈·⌉` (`j = 2`),
`r⁺(x) = ⌊x + 1/2⌋` (`j = 3`, Mathlib's `round`, see `round_eq`) and
`r⁻(x) = ⌈x - 1/2⌉` (`j = 4`).

Conventions: the multiset `C = {a_1, …, a_ℓ}` is a tuple `a : Fin ℓ → ℤ`; the modulus `m` is a
natural number, and at `m = 0` Lean's `x / 0 = 0` makes every term `F 0 = 0`, so statements whose
value is then trivially correct carry no positivity hypothesis on `m`. The partial sums are written
inline: `S^(F)(C, m, K) = ∑ k ∈ Finset.range (K + 1), tverbergSum F a m k` and
`T^(F)(C, m, K) = ∑ k ∈ Finset.Icc 1 K, tverbergSum F a m k`. `⌊m/2⌋` is the natural-number
quotient `m / 2`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Ceiling analogue of Hermite's identity: for every real `x` and natural `n`,
`Σ_{1 ≤ k ≤ n} ⌈x + k/n⌉ = ⌈n x⌉ + n`. The paper states it for `n ∈ ℕ` positive; at `n = 0`
both sides are `0`, so no hypothesis is needed. The record's brackets are garbled; the
summand is read as a ceiling from the lemma's title ("an analog of Hermite's identity for the
ceiling function") and its right-hand side `⌈nx⌉ + n`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 6. -/
public theorem_wanted sum_ceil_add_div_eq_ceil_mul_add (x : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ⌈x + (k : ℝ) / n⌉ = ⌈(n : ℝ) * x⌉ + n

/-- The inclusion-exclusion-like sum
`g^(F)(x_1, …, x_n) = Σ_{∅ ≠ T ⊆ [1, n]} (-1)^{|T| - 1} F(Σ_{i ∈ T} x_i)` (Definition 2 for
`F = ⌊·⌋`, the general `g^(F)` of Section 1 and Definition 3 for the other `F`).

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 2 and 3. -/
public def inclExclLikeSum {n : ℕ} (F : ℝ → ℤ) (x : Fin n → ℝ) : ℤ :=
  ∑ T : Finset (Fin n) with T.Nonempty, (-1) ^ (T.card - 1) * F (∑ i ∈ T, x i)

/-- Characteristic value: `g^(F)(x) = F(x)` in one variable.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 2 and 3. -/
public theorem inclExclLikeSum_one (F : ℝ → ℤ) (x : ℝ) : inclExclLikeSum F ![x] = F x := by
  have h : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  rw [inclExclLikeSum, h, Finset.sum_filter, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp

/-- Characteristic value: `g^(F)(x, y) = F(x) + F(y) - F(x + y)`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 2 and 3. -/
public theorem inclExclLikeSum_two (F : ℝ → ℤ) (x y : ℝ) :
    inclExclLikeSum F ![x, y] = F x + F y - F (x + y) := by
  have h : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [inclExclLikeSum, h, Finset.sum_filter, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

/-- Tverberg's sum
`f^(F)({a_1, …, a_ℓ}, m, k) = Σ_{T ⊆ [1, ℓ]} (-1)^{ℓ - |T|} F((k + Σ_{i ∈ T} a_i) / m)`
(Definition 1 for `F = ⌊·⌋`, Section 1 and Definition 3 for the other `F`).

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 1 and 3. -/
public noncomputable def tverbergSum {ℓ : ℕ} (F : ℝ → ℤ) (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ) : ℤ :=
  ∑ T : Finset (Fin ℓ), (-1) ^ (ℓ - T.card) * F (((k + ∑ i ∈ T, a i : ℤ) : ℝ) / m)

/-- Characteristic value: with no `a_i`, `f^(F)(∅, m, k) = F(k / m)`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 1 and 3. -/
public theorem tverbergSum_zero (F : ℝ → ℤ) (a : Fin 0 → ℤ) (m : ℕ) (k : ℤ) :
    tverbergSum F a m k = F (k / m) := by
  simp [tverbergSum, Finset.univ_unique, Finset.eq_empty_of_isEmpty]

/-- Characteristic value: `f^(F)({a}, m, k) = F((k + a) / m) - F(k / m)`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 1 and 3. -/
public theorem tverbergSum_one (F : ℝ → ℤ) (a : ℤ) (m : ℕ) (k : ℤ) :
    tverbergSum F ![a] m k = F ((k + a : ℤ) / m) - F (k / m) := by
  have h : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  simp [tverbergSum, h]
  ring

/-- Lemma 1: for `n ≥ 2`, (i) `g_3(x) = g_1(x) - g_1(x, 1/2)`,
(ii) `g_4(x) = g_2(x) - g_2(x, -1/2)`, and (iii) each `g_j` has period `1` in each variable.
Parts (i) and (ii) also hold for `n < 2`; part (iii) fails at `n = 1` (`g_1(x) = ⌊x⌋`), so the paper's `n ≥ 2` is kept.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 1. -/
public theorem_wanted inclExclLikeSum_relations_and_periodic {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → ℝ) :
    inclExclLikeSum round x =
        inclExclLikeSum Int.floor x - inclExclLikeSum Int.floor (Fin.snoc x (1 / 2 : ℝ)) ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x =
        inclExclLikeSum Int.ceil x - inclExclLikeSum Int.ceil (Fin.snoc x (-1 / 2 : ℝ)) ∧
      ∀ F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)),
        ∀ (i : Fin n) (q : ℤ),
        inclExclLikeSum F (Function.update x i (x i + q)) = inclExclLikeSum F x

/-- Lemma 2: `f_j({a_1, …, a_ℓ}, m, 0) = (-1)^{ℓ-1} g_j(a_1/m, …, a_ℓ/m)` and
`f_j({a_1, …, a_ℓ}, m, k) = (-1)^ℓ g_j(a_1/m, …, a_ℓ/m, k/m) + (-1)^{ℓ-1} g_j(a_1/m, …, a_ℓ/m)`.
The sign `(-1)^{ℓ-1}` is written `(-1)^(ℓ+1)`; with that sign both identities hold for every
`ℓ` and every natural `m`, so the paper's `ℓ ≥ 2` and `m > 0` are dropped.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 2. -/
public theorem_wanted tverbergSum_eq_inclExclLikeSum {ℓ : ℕ} (F : ℝ → ℤ)
    (hF : F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)))
    (a : Fin ℓ → ℤ) (m : ℕ) :
    tverbergSum F a m 0 = (-1) ^ (ℓ + 1) * inclExclLikeSum F (fun i => (a i : ℝ) / m) ∧
      ∀ k : ℤ, tverbergSum F a m k =
        (-1) ^ ℓ * inclExclLikeSum F (Fin.snoc (fun i => (a i : ℝ) / m) ((k : ℝ) / m)) +
          (-1) ^ (ℓ + 1) * inclExclLikeSum F (fun i => (a i : ℝ) / m)

/-- Lemma 3: for `ℓ ≥ 2`, each `f_j` has period `m` in every `a_i` and in `k`. The paper's
standing hypothesis `ℓ ≥ 2` is needed: at `ℓ = 1`, `f_1({a}, m, k) = ⌊(k+a)/m⌋ - ⌊k/m⌋` shifts by
`q` when `a` does by `qm`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 3. -/
public theorem_wanted tverbergSum_periodic {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (F : ℝ → ℤ)
    (hF : F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)))
    (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ) (i : Fin ℓ) (q : ℤ) :
    tverbergSum F (Function.update a i (a i + q * m)) m k = tverbergSum F a m k ∧
      tverbergSum F a m (k + q * m) = tverbergSum F a m k

/-- Lemma 4 (Onphaeng and Pongsriiam): for `ℓ ≥ 2`, `-2^{ℓ-2} ≤ f_1 ≤ 2^{ℓ-2}`, with equality
for `m = 2r` even and every `a_i = r`: `f_1(C, m, 0) = (-1)^ℓ 2^{ℓ-2}` and
`f_1(C, m, m/2) = (-1)^{ℓ+1} 2^{ℓ-2}` (the paper's odd and even cases in one formula). The bound
is stated for every natural `m` (trivial at `m = 0`).

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 4. -/
public theorem_wanted tverbergSum_floor_bounds {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (∀ (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ),
      -2 ^ (ℓ - 2) ≤ tverbergSum Int.floor a m k ∧ tverbergSum Int.floor a m k ≤ 2 ^ (ℓ - 2)) ∧
      ∀ r : ℕ, 0 < r →
        tverbergSum Int.floor (fun _ : Fin ℓ => (r : ℤ)) (2 * r) 0 = (-1) ^ ℓ * 2 ^ (ℓ - 2) ∧
          tverbergSum Int.floor (fun _ : Fin ℓ => (r : ℤ)) (2 * r) r = (-1) ^ (ℓ + 1) * 2 ^ (ℓ - 2)

/-- Lemma 5 (Onphaeng and Pongsriiam): for `n ≥ 2`, `g_1` has minimum `-2^{n-2}`, attained at
`x_k = 1/2`, and maximum `2^{n-2} - 1`, attained at `x_k = 1/2 - 1/n²`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 5. -/
public theorem_wanted inclExclLikeSum_floor_extrema {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ, -2 ^ (n - 2) ≤ inclExclLikeSum Int.floor x ∧
      inclExclLikeSum Int.floor x ≤ 2 ^ (n - 2) - 1) ∧
      inclExclLikeSum Int.floor (fun _ : Fin n => (1 / 2 : ℝ)) = -2 ^ (n - 2) ∧
      inclExclLikeSum Int.floor (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) = 2 ^ (n - 2) - 1

/-- Lemma 7: for `ℓ ≥ 2`, (i) `S_j(C, m, m - 1) = 0` for every `j`; (ii) `T_j(C, m, m) = 0` for
`j = 2, 4`; (iii) `S_j` has period `m` in `K` and in every `a_i`; (iv) so does `T_j` for
`j = 2, 4`. Periodicity in `K` is stated for shifts `K ↦ K + qm` with `q ∈ ℕ` (the paper's
`q ∈ ℤ` with `K + qm ≥ 0` is the same statement read from the smaller argument). Parts (i) and (ii)
hold trivially at `m = 0`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 7. -/
public theorem_wanted tverbergPartialSum_vanish_and_periodic {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (a : Fin ℓ → ℤ) (m : ℕ) :
    (∀ F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)),
      ∑ k ∈ Finset.range m, tverbergSum F a m k = 0 ∧
        ∀ K q : ℕ, ∑ k ∈ Finset.range (K + q * m + 1), tverbergSum F a m k =
          ∑ k ∈ Finset.range (K + 1), tverbergSum F a m k ∧
        ∀ (K : ℕ) (i : Fin ℓ) (q : ℤ),
          ∑ k ∈ Finset.range (K + 1), tverbergSum F (Function.update a i (a i + q * m)) m k =
            ∑ k ∈ Finset.range (K + 1), tverbergSum F a m k) ∧
      ∀ F ∈ ({Int.ceil, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)),
        ∑ k ∈ Finset.Icc 1 m, tverbergSum F a m k = 0 ∧
          ∀ K q : ℕ, ∑ k ∈ Finset.Icc 1 (K + q * m), tverbergSum F a m k =
            ∑ k ∈ Finset.Icc 1 K, tverbergSum F a m k ∧
          ∀ (K : ℕ) (i : Fin ℓ) (q : ℤ),
            ∑ k ∈ Finset.Icc 1 K, tverbergSum F (Function.update a i (a i + q * m)) m k =
              ∑ k ∈ Finset.Icc 1 K, tverbergSum F a m k

/-- Lemma 8: for `q ∈ ℤ` and `m ∈ ℕ` positive, `⌊q/m + 1/2⌋ = ⌊(q + ⌊m/2⌋)/m⌋` and
`⌈q/m + 1/2⌉ = ⌈(q + ⌈m/2⌉)/m⌉`, with `⌊m/2⌋ = m / 2` and `⌈m/2⌉ = (m + 1) / 2` in `ℕ`. The
record's brackets are garbled; the bracket types are taken from the paper's statement and proof.
The ceiling identity fails at `m = 0` (`⌈1/2⌉ = 1`), so `0 < m` is kept.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 8. -/
public theorem_wanted floor_ceil_div_add_half (q : ℤ) (m : ℕ) (hm : 0 < m) :
    ⌊(q : ℝ) / m + 1 / 2⌋ = ⌊((q + (m / 2 : ℕ) : ℤ) : ℝ) / m⌋ ∧
      ⌈(q : ℝ) / m + 1 / 2⌉ = ⌈((q + ((m + 1) / 2 : ℕ) : ℤ) : ℝ) / m⌉

/-- Theorem 1: for `n ≥ 2`, `g_2` (ceiling) has maximum `2^{n-2}`, attained at `x_k = 1/2`, and
minimum `-2^{n-2} + 1`, attained at `x_k = 1/2 + 1/n²`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 1. -/
public theorem_wanted inclExclLikeSum_ceil_extrema {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ, -2 ^ (n - 2) + 1 ≤ inclExclLikeSum Int.ceil x ∧
      inclExclLikeSum Int.ceil x ≤ 2 ^ (n - 2)) ∧
      inclExclLikeSum Int.ceil (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) = -2 ^ (n - 2) + 1 ∧
      inclExclLikeSum Int.ceil (fun _ : Fin n => (1 / 2 : ℝ)) = 2 ^ (n - 2)

/-- Theorem 2: for `n ≥ 2`, `g_3` (nearest integer, ties up: `round`) has maximum `2^{n-2}`,
attained at `x_k = 1/2`, and minimum `-2^{n-2}`, attained at `x_k = 1/2 - 1/n²`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 2. -/
public theorem_wanted inclExclLikeSum_round_extrema {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ, -2 ^ (n - 2) ≤ inclExclLikeSum round x ∧
      inclExclLikeSum round x ≤ 2 ^ (n - 2)) ∧
      inclExclLikeSum round (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) = -2 ^ (n - 2) ∧
      inclExclLikeSum round (fun _ : Fin n => (1 / 2 : ℝ)) = 2 ^ (n - 2)

/-- Theorem 3: for `n ≥ 2`, `g_4` (nearest integer, ties down: `⌈x - 1/2⌉`) has minimum
`-2^{n-2}`, attained at `x_k = 1/2`, and maximum `2^{n-2}`, attained at `x_k = 1/2 + 1/n²`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 3. -/
public theorem_wanted inclExclLikeSum_roundDown_extrema {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ, -2 ^ (n - 2) ≤ inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x ≤ 2 ^ (n - 2)) ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin n => (1 / 2 : ℝ)) = -2 ^ (n - 2) ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) =
        2 ^ (n - 2)

/-- Corollary 1: for `n ≥ 2`, `-2^{n-2} ≤ g_1 ≤ 2^{n-2} - 1`, `-2^{n-2} + 1 ≤ g_2 ≤ 2^{n-2}` and
`-2^{n-2} ≤ g_3, g_4 ≤ 2^{n-2}`; at `x_k = 1/2`, `g_1 = -2^{n-2} = g_4` and `g_2 = 2^{n-2} = g_3`;
at `x_k = 1/2 - 1/n²`, `g_1 = 2^{n-2} - 1 = -g_3 - 1`; at `x_k = 1/2 + 1/n²`,
`g_2 = -2^{n-2} + 1 = -g_4 + 1`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Corollary 1. -/
public theorem_wanted inclExclLikeSum_bounds_summary {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ,
      (-2 ^ (n - 2) ≤ inclExclLikeSum Int.floor x ∧
        inclExclLikeSum Int.floor x ≤ 2 ^ (n - 2) - 1) ∧
      (-2 ^ (n - 2) + 1 ≤ inclExclLikeSum Int.ceil x ∧
        inclExclLikeSum Int.ceil x ≤ 2 ^ (n - 2)) ∧
      (-2 ^ (n - 2) ≤ inclExclLikeSum round x ∧ inclExclLikeSum round x ≤ 2 ^ (n - 2)) ∧
      (-2 ^ (n - 2) ≤ inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x ∧
        inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x ≤ 2 ^ (n - 2))) ∧
    (inclExclLikeSum Int.floor (fun _ : Fin n => (1 / 2 : ℝ)) = -2 ^ (n - 2) ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin n => (1 / 2 : ℝ)) = -2 ^ (n - 2) ∧
      inclExclLikeSum Int.ceil (fun _ : Fin n => (1 / 2 : ℝ)) = 2 ^ (n - 2) ∧
      inclExclLikeSum round (fun _ : Fin n => (1 / 2 : ℝ)) = 2 ^ (n - 2)) ∧
    (inclExclLikeSum Int.floor (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) = 2 ^ (n - 2) - 1 ∧
      inclExclLikeSum Int.floor (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) =
        -inclExclLikeSum round (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) - 1) ∧
    (inclExclLikeSum Int.ceil (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) = -2 ^ (n - 2) + 1 ∧
      inclExclLikeSum Int.ceil (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) =
        -inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) + 1)

/-- Theorem 4: for `ℓ ≥ 2`, `-2^{ℓ-2} ≤ f_2 ≤ 2^{ℓ-2}`, with equality for `m = 2r` even and every
`a_i = r`: `f_2(C, m, 0) = (-1)^{ℓ+1} 2^{ℓ-2}` and `f_2(C, m, m/2) = (-1)^ℓ 2^{ℓ-2}` (the paper's
odd and even cases in one formula). The bound is stated for every natural `m` (trivial at `m = 0`).

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 4. -/
public theorem_wanted tverbergSum_ceil_bounds {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (∀ (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ),
      -2 ^ (ℓ - 2) ≤ tverbergSum Int.ceil a m k ∧ tverbergSum Int.ceil a m k ≤ 2 ^ (ℓ - 2)) ∧
      ∀ r : ℕ, 0 < r →
        tverbergSum Int.ceil (fun _ : Fin ℓ => (r : ℤ)) (2 * r) 0 = (-1) ^ (ℓ + 1) * 2 ^ (ℓ - 2) ∧
          tverbergSum Int.ceil (fun _ : Fin ℓ => (r : ℤ)) (2 * r) r = (-1) ^ ℓ * 2 ^ (ℓ - 2)

/-- Theorem 5: for `ℓ ≥ 2`, `-2^{ℓ-2} ≤ f_3 ≤ 2^{ℓ-2}`, with equality for `m = 2r` even and every
`a_i = r`: `f_3(C, m, 0) = (-1)^{ℓ+1} 2^{ℓ-2}` and `f_3(C, m, m/2) = (-1)^ℓ 2^{ℓ-2}` (the paper's
odd and even cases in one formula). The bound is stated for every natural `m` (trivial at `m = 0`).

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 5. -/
public theorem_wanted tverbergSum_round_bounds {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (∀ (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ),
      -2 ^ (ℓ - 2) ≤ tverbergSum round a m k ∧ tverbergSum round a m k ≤ 2 ^ (ℓ - 2)) ∧
      ∀ r : ℕ, 0 < r →
        tverbergSum round (fun _ : Fin ℓ => (r : ℤ)) (2 * r) 0 = (-1) ^ (ℓ + 1) * 2 ^ (ℓ - 2) ∧
          tverbergSum round (fun _ : Fin ℓ => (r : ℤ)) (2 * r) r = (-1) ^ ℓ * 2 ^ (ℓ - 2)

/-- Theorem 6: for `ℓ ≥ 2`, `-2^{ℓ-2} ≤ f_4 ≤ 2^{ℓ-2}`, with equality for `m = 2r` even and every
`a_i = r`: `f_4(C, m, 0) = (-1)^ℓ 2^{ℓ-2}` and `f_4(C, m, m/2) = (-1)^{ℓ+1} 2^{ℓ-2}` (the paper's
odd and even cases in one formula). The bound is stated for every natural `m` (trivial at `m = 0`).

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 6. -/
public theorem_wanted tverbergSum_roundDown_bounds {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (∀ (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ),
      -2 ^ (ℓ - 2) ≤ tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) a m k ∧
        tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) a m k ≤ 2 ^ (ℓ - 2)) ∧
      ∀ r : ℕ, 0 < r →
        tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin ℓ => (r : ℤ)) (2 * r) 0 =
            (-1) ^ ℓ * 2 ^ (ℓ - 2) ∧
          tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin ℓ => (r : ℤ)) (2 * r) r =
            (-1) ^ (ℓ + 1) * 2 ^ (ℓ - 2)

/-- Theorem 7: for `a, b ∈ ℤ` and `m, K ∈ ℕ`, `0 ≤ T_2({a, b}, m, K) ≤ ⌊m/2⌋`; for `m = 2r` and
`a = b = r`, `T_2({a, b}, m, m) = 0` and `T_2({a, b}, m, m/2) = ⌊m/2⌋ = r`. The paper takes
`m, K ≥ 1`; at `m = 0` or `K = 0` the sum is `0` and every claim holds, so no positivity hypotheses.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 7. -/
public theorem_wanted tverbergTailSum_ceil_two_bounds :
    (∀ (a b : ℤ) (m K : ℕ), 0 ≤ ∑ k ∈ Finset.Icc 1 K, tverbergSum Int.ceil ![a, b] m k ∧
      ∑ k ∈ Finset.Icc 1 K, tverbergSum Int.ceil ![a, b] m k ≤ ((m / 2 : ℕ) : ℤ)) ∧
      ∀ r : ℕ, ∑ k ∈ Finset.Icc 1 (2 * r), tverbergSum Int.ceil ![(r : ℤ), r] (2 * r) k = 0 ∧
        ∑ k ∈ Finset.Icc 1 r, tverbergSum Int.ceil ![(r : ℤ), r] (2 * r) k = r

/-- Theorem 8: for `ℓ ≥ 2`, `-2^{ℓ-2} ⌊m/2⌋ ≤ T_2(C, m, K) ≤ 2^{ℓ-2} ⌊m/2⌋`, with equality for
`m = 2r` and every `a_i = r`: `T_2(C, m, m/2) = (-1)^ℓ 2^{ℓ-2} r`. Corrected reading: the record's
parts (i) and (ii) assert the equality for every `K`, which is false (`ℓ = 3`, `m = 2`,
`a_i = 1`, `K = 2` gives `T_2 = 0`, not `-2`, and Lemma 7 (ii) gives `T_2(C, m, m) = 0`); the
paper's proof establishes it at `K = m/2`, which is what is stated. The bound is stated for every
natural `m` and `K` (trivial at `0`).

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 8. -/
public theorem_wanted tverbergTailSum_ceil_bounds {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (∀ (a : Fin ℓ → ℤ) (m K : ℕ),
      -(2 ^ (ℓ - 2) * ((m / 2 : ℕ) : ℤ)) ≤ ∑ k ∈ Finset.Icc 1 K, tverbergSum Int.ceil a m k ∧
        ∑ k ∈ Finset.Icc 1 K, tverbergSum Int.ceil a m k ≤ 2 ^ (ℓ - 2) * ((m / 2 : ℕ) : ℤ)) ∧
      ∀ r : ℕ, ∑ k ∈ Finset.Icc 1 r, tverbergSum Int.ceil (fun _ : Fin ℓ => (r : ℤ)) (2 * r) k =
        (-1) ^ ℓ * 2 ^ (ℓ - 2) * r

/-- Theorem 9: for `a, b ∈ ℤ`, `m ∈ ℕ` and `K ≥ 0`, `-⌊m/2⌋ ≤ S_3({a, b}, m, K) ≤ ⌊m/2⌋`, and the
lower bound is attained. The paper's existential "there are `a, b, m, K`" is trivial at `m = 1`
(`⌊1/2⌋ = 0`); it is stated through the witness of the paper's proof, for every even `m = 2(r + 1)`:
`a = b = r + 1`, `K = m/2 - 1 = r`. The bound is stated for every natural `m` (trivial at `0`).

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 9. -/
public theorem_wanted tverbergPartialSum_round_two_bounds :
    (∀ (a b : ℤ) (m K : ℕ),
      -((m / 2 : ℕ) : ℤ) ≤ ∑ k ∈ Finset.range (K + 1), tverbergSum round ![a, b] m k ∧
        ∑ k ∈ Finset.range (K + 1), tverbergSum round ![a, b] m k ≤ ((m / 2 : ℕ) : ℤ)) ∧
      ∀ r : ℕ, ∑ k ∈ Finset.range (r + 1),
        tverbergSum round ![((r + 1 : ℕ) : ℤ), ((r + 1 : ℕ) : ℤ)] (2 * (r + 1)) k =
          -((r + 1 : ℕ) : ℤ)

/-- Theorem 10: for `a, b ∈ ℤ` and `m, K ∈ ℕ`, `-⌊m/2⌋ ≤ T_4({a, b}, m, K) ≤ ⌊m/2⌋`, and the lower
bound is attained. The paper's existential is stated through the witness of its proof, for every
even `m = 2r`: `a = b = K = r`. The paper takes `m, K ≥ 1`; the claims hold trivially at `0`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 10. -/
public theorem_wanted tverbergTailSum_roundDown_two_bounds :
    (∀ (a b : ℤ) (m K : ℕ),
      -((m / 2 : ℕ) : ℤ) ≤
          ∑ k ∈ Finset.Icc 1 K, tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) ![a, b] m k ∧
        ∑ k ∈ Finset.Icc 1 K, tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) ![a, b] m k ≤
          ((m / 2 : ℕ) : ℤ)) ∧
      ∀ r : ℕ,
        ∑ k ∈ Finset.Icc 1 r, tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) ![(r : ℤ), r] (2 * r) k =
          -(r : ℤ)

end

end MetaMathlibExt
