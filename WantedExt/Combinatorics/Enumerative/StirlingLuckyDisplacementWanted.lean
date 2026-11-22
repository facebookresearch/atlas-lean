/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.StirlingPermutation
public import WantedExt.Combinatorics.Enumerative.LuckyCarsWanted

/-!
# Lucky and displacement statistics of Stirling permutations

Statements from L. Colmenarejo, A. Dawkins, J. Elder, P. E. Harris, K. J. Harry,
S. Kara, D. Smith, and B. E. Tenner, *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7
(arXiv:2403.03280).

A Stirling permutation of order `n` is MathlibExt's
`MetaMathlibExt.IsStirlingPermutation n w` for a word `w : Fin (2 * n) → ℕ`
(`w(1) ⋯ w(2n)` is `w 0, …, w (2n-1)`). It is read as a parking function of
length `2n`: car `i + 1` prefers spot `w i`. Parking is the existing greedy
outcome `MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted.parkSpots`
(zero-based), applied to the zero-based preferences `stirlingPref w`. Car and
spot numbers in the statements below are the paper's one-based numbers: the car
at index `i : Fin (2 * n)` is car `i + 1`, and `stirlingParkSpot w i` is its
one-based spot `p(i + 1)`.
-/

open MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted (parkSpots)

namespace MetaMathlibExt

@[expose] public section

/-- Zero-based preferences of the word `w`: car `i + 1` prefers the zero-based
spot `w i - 1` (reduced modulo `2n`, which changes nothing for Stirling
permutations, whose values lie in `{1, …, n}`).

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Section 1 (Stirling permutations read as parking functions of length `2n`). -/
public def stirlingPref {n : ℕ} (w : Fin (2 * n) → ℕ) (i : Fin (2 * n)) : Fin (2 * n) :=
  ⟨(w i - 1) % (2 * n), Nat.mod_lt _ i.pos⟩

/-- The one-based spot `p(i + 1)` in which car `i + 1` parks.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 5.1. -/
public def stirlingParkSpot {n : ℕ} (w : Fin (2 * n) → ℕ) (i : Fin (2 * n)) : ℕ :=
  (parkSpots (stirlingPref w) i).val + 1

/-- `Lucky(w)`: the set of (one-based) cars that park in their preferred spot.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 1.2. -/
public def stirlingLuckySet {n : ℕ} (w : Fin (2 * n) → ℕ) : Finset ℕ :=
  (Finset.univ.filter fun i => stirlingParkSpot w i = w i).image fun i => i.val + 1

/-- The displacement `d(i + 1) = p(i + 1) - w(i + 1)` of car `i + 1`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 5.1; the tuple `i ↦ d(i + 1)` is the displacement composition
`dis(w)` (Definition 5.4). -/
public def stirlingDisplacement {n : ℕ} (w : Fin (2 * n) → ℕ) (i : Fin (2 * n)) : ℕ :=
  stirlingParkSpot w i - w i

/-- The total displacement `d(w) = ∑_i d(i)`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 5.1. -/
public def stirlingTotalDisplacement {n : ℕ} (w : Fin (2 * n) → ℕ) : ℕ :=
  ∑ i, stirlingDisplacement w i

/-- `S` is an `n`-admissible lucky set: `S = Lucky(w)` for some `w ∈ Q_n`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 3.1. -/
public def IsAdmissibleLuckySet (n : ℕ) (S : Finset ℕ) : Prop :=
  ∃ w : Fin (2 * n) → ℕ, IsStirlingPermutation n w ∧ stirlingLuckySet w = S

/-- Characteristic values: `Lucky(1122) = {1}` and `Lucky(1221) = {1, 2}`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definitions 1.2 and 3.1. -/
public theorem stirlingLuckySet_small :
    stirlingLuckySet (n := 2) ![1, 1, 2, 2] = {1} ∧
      stirlingLuckySet (n := 2) ![1, 2, 2, 1] = {1, 2} := by
  decide

/-- Characteristic values: `dis(1122) = (0, 1, 1, 2)` and `dis(11244233) =
(0, 1, 1, 0, 1, 4, 4, 5)` (the paper's Example 5.5).

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Definition 5.4 and Example 5.5. -/
public theorem stirlingDisplacement_small :
    (fun i => stirlingDisplacement (n := 2) ![1, 1, 2, 2] i) = ![0, 1, 1, 2] ∧
      (fun i => stirlingDisplacement (n := 4) ![1, 1, 2, 4, 4, 2, 3, 3] i) =
        ![0, 1, 1, 0, 1, 4, 4, 5] := by
  decide

/-- For `w ∈ Q_n` (`n ≥ 1`): (a) car `1` is lucky; (b) the first car `i` with
`w(i) = 1` is lucky; (c) `1 ≤ lucky(w) ≤ n`. (`n ≥ 1` is added: `Q_0` has only
the empty word, with no cars.)

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 2.1 (`jis-2024-24.6.7-lem-5`). -/
public theorem_wanted stirlingLuckySet_basic (n : ℕ) (hn : 1 ≤ n) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) :
    1 ∈ stirlingLuckySet w ∧
      (∀ i : Fin (2 * n), w i = 1 → (∀ j < i, w j ≠ 1) → i.val + 1 ∈ stirlingLuckySet w) ∧
      1 ≤ (stirlingLuckySet w).card ∧ (stirlingLuckySet w).card ≤ n

/-- For `n ≥ 1`, `w ∈ Q_n` is extremely unlucky (`Lucky(w) = {1}`) if and only if
for every `x ∈ [2, n]`, `w(i) < x` for all `i ≤ x`. (`n ≥ 1` is added: the empty
word of `Q_0` has no lucky cars, while the right-hand side holds vacuously.)

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 2.5 (`jis-2024-24.6.7-cor-11`). -/
public theorem_wanted stirlingLuckySet_eq_singleton_iff (n : ℕ) (hn : 1 ≤ n)
    (w : Fin (2 * n) → ℕ) (hw : IsStirlingPermutation n w) :
    stirlingLuckySet w = {1} ↔
      ∀ x ∈ Finset.Icc 2 n, ∀ i : Fin (2 * n), i.val + 1 ≤ x → w i < x

/-- For `n ≥ 1` there are `(n - 1)!` extremely unlucky Stirling permutations of
order `n`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Theorem 2.7 (`jis-2024-24.6.7-thm-13`). -/
public theorem_wanted card_extremely_unlucky_stirling (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {w : Fin (2 * n) → ℕ // IsStirlingPermutation n w ∧ stirlingLuckySet w = {1}} =
      (n - 1).factorial

/-- `w ∈ Q_n` is extremely lucky (`lucky(w) = n`) if and only if the second
appearances of the values occur in decreasing order (the subword of second
appearances is `n ⋯ 2 1`).

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Proposition 2.11 (`jis-2024-24.6.7-prop-17`). -/
public theorem_wanted stirlingLuckySet_card_eq_iff (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) :
    (stirlingLuckySet w).card = n ↔
      ∀ a b : Fin (2 * n), (∃ c < a, w c = w a) → (∃ c < b, w c = w b) → a < b → w b < w a

/-- Extremely lucky Stirling permutations of order `n` are in bijection with
valid parenthesizations of `n` pairs of parentheses (Dyck words of semilength
`n`).

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Theorem 2.12 (`jis-2024-24.6.7-thm-18`). -/
public theorem_wanted extremely_lucky_stirling_equiv_dyckWord (n : ℕ) :
    Nonempty ({w : Fin (2 * n) → ℕ // IsStirlingPermutation n w ∧ (stirlingLuckySet w).card = n} ≃
      {p : DyckWord // p.semilength = n})

/-- For every positive integer `n`, the number of extremely lucky Stirling
permutations of order `n` is the Catalan number `C_n`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 2.14 (`jis-2024-24.6.7-cor-20`). -/
public theorem_wanted card_extremely_lucky_stirling (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {w : Fin (2 * n) → ℕ // IsStirlingPermutation n w ∧ (stirlingLuckySet w).card = n} =
      catalan n

/-- If `S` is `n`-admissible (`n ≥ 1`), then `S` and `S ∪ {2n + 1}` are both
`(n + 1)`-admissible. (`n ≥ 1` is added: the empty set is `0`-admissible but not
`1`-admissible.)

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Theorem 3.3 (`jis-2024-24.6.7-thm-23`). -/
public theorem_wanted IsAdmissibleLuckySet.succ (n : ℕ) (hn : 1 ≤ n) (S : Finset ℕ)
    (hS : IsAdmissibleLuckySet n S) :
    IsAdmissibleLuckySet (n + 1) S ∧ IsAdmissibleLuckySet (n + 1) (insert (2 * n + 1) S)

/-- If `S` is `n`-admissible (`n ≥ 1`), then `1 ∈ S` and `2n ∉ S`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 3.4 (`jis-2024-24.6.7-cor-24`). -/
public theorem_wanted IsAdmissibleLuckySet.one_mem_and_two_mul_not_mem (n : ℕ) (hn : 1 ≤ n)
    (S : Finset ℕ) (hS : IsAdmissibleLuckySet n S) : 1 ∈ S ∧ 2 * n ∉ S

/-- Let `w ∈ Q_n` with `lucky(w) ≥ 2` and let `x` be the second-smallest element
of `Lucky(w)` (written: `x ∈ Lucky(w)` with exactly one smaller lucky car). Then
cars `2, …, x - 1` park, in order, in spots `w(1) + 1, …, w(1) + x - 2`: car
`c = i + 1` parks in spot `w(1) + c - 1 = w(1) + i`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 3.5 (`jis-2024-24.6.7-lem-25`). -/
public theorem_wanted stirlingParkSpot_before_second_lucky (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (x : ℕ) (hx : x ∈ stirlingLuckySet w)
    (hx2 : ((stirlingLuckySet w).filter (· < x)).card = 1) (i : Fin (2 * n))
    (hi : 2 ≤ i.val + 1) (hix : i.val + 1 ≤ x - 1) :
    stirlingParkSpot w i = w ⟨0, i.pos⟩ + i.val

/-- Let `w ∈ Q_n` and let `j` be the first car preferring spot `k = w(j)`. If
`w(i) > w(j)` for all `i < j`, then `j` is odd (one-based). The hypothesis
`w(i) > w(j)` for `i < j` already makes `j` the first car preferring `w(j)`, and
`k ∈ [1, n]` holds automatically, so neither is restated.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 3.7 (`jis-2024-24.6.7-lem-27`). -/
public theorem_wanted stirling_odd_of_lt_all_before (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (j : Fin (2 * n)) (hj : ∀ i < j, w j < w i) :
    Odd (j.val + 1)

/-- Let `w ∈ Q_n` with `lucky(w) ≥ 2` and `x` the second-smallest element of
`Lucky(w)`. If `x > n`, then `x` is odd.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Proposition 3.8 (`jis-2024-24.6.7-prop-28`). -/
public theorem_wanted stirling_second_lucky_odd (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (x : ℕ) (hx : x ∈ stirlingLuckySet w)
    (hx2 : ((stirlingLuckySet w).filter (· < x)).card = 1) (hxn : n < x) : Odd x

/-- Let `w ∈ Q_n` with `lucky(w) ≥ 2` and `x` the second-smallest element of
`Lucky(w)`. If `w(1) = 1`, then `x ≤ w(x) ≤ n`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 3.9 (`jis-2024-24.6.7-lem-29`). -/
public theorem_wanted stirling_second_lucky_pref (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (x : ℕ) (hx : x ∈ stirlingLuckySet w)
    (hx2 : ((stirlingLuckySet w).filter (· < x)).card = 1) (i : Fin (2 * n))
    (hi : i.val + 1 = x) (hw1 : w ⟨0, i.pos⟩ = 1) : x ≤ w i ∧ w i ≤ n

/-- Let `w ∈ Q_n` with `lucky(w) ≥ 3` and `x` the second-smallest element of
`Lucky(w)`. If `x ≥ n`, then `w(1) ≥ lucky(w)`, and every lucky car parks in one
of the first `w(1)` spots.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 3.10 (`jis-2024-24.6.7-lem-30`). -/
public theorem_wanted stirling_first_pref_ge_lucky (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (h3 : 3 ≤ (stirlingLuckySet w).card) (x : ℕ)
    (hx : x ∈ stirlingLuckySet w) (hx2 : ((stirlingLuckySet w).filter (· < x)).card = 1)
    (hxn : n ≤ x) (i₀ : Fin (2 * n)) (hi₀ : i₀.val = 0) :
    (stirlingLuckySet w).card ≤ w i₀ ∧
      ∀ i : Fin (2 * n), i.val + 1 ∈ stirlingLuckySet w → stirlingParkSpot w i ≤ w i₀

/-- For `w ∈ Q_n`, car `2n - 1` is lucky if and only if `w(2n - 1) = 1`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Theorem 3.11 (`jis-2024-24.6.7-thm-31`). -/
public theorem_wanted stirling_penultimate_lucky_iff (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (i : Fin (2 * n)) (hi : i.val + 1 = 2 * n - 1) :
    2 * n - 1 ∈ stirlingLuckySet w ↔ w i = 1

/-- A two-element set `{h, i}` with `h < i ≤ 2n` is `n`-admissible if and only if
`h = 1` and either `i > n` with `i` odd, or `i ≤ n`. The bound `i ≤ 2n` is the
paper's standing `S ⊆ [2n]` (without it `{1, 2n + 1}` would satisfy the right
side).

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Theorem 4.1 (`jis-2024-24.6.7-thm-32`). -/
public theorem_wanted isAdmissibleLuckySet_pair_iff (n h i : ℕ) (hhi : h < i) (hi : i ≤ 2 * n) :
    IsAdmissibleLuckySet n {h, i} ↔ h = 1 ∧ (n < i ∧ Odd i ∨ i ≤ n)

/-- For `n ≥ 1` there are `n - 1 + ⌈(n - 1)/2⌉` `n`-admissible lucky sets of
size two.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 4.2 (`jis-2024-24.6.7-cor-33`). -/
public theorem_wanted ncard_admissibleLuckySet_card_two (n : ℕ) (hn : 1 ≤ n) :
    {S : Finset ℕ | IsAdmissibleLuckySet n S ∧ S.card = 2}.ncard =
      n - 1 + ⌈((n - 1 : ℕ) : ℚ) / 2⌉₊

/-- Let `w ∈ Q_n` with `S = Lucky(w)` whose second-smallest element is `n`.
(a) If `n` is even, then `w(1) = 1`, `w(n) = n` and `|S| = 2`. (b) If `n` is odd
and `w(1) = 1`, then `w(n) = n` and `|S| = 2`. The paper's `w` is the witness of
admissibility; the statement quantifies over every such witness.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 4.3 (`jis-2024-24.6.7-lem-34`). -/
public theorem_wanted stirling_second_lucky_eq_n (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (hn : n ∈ stirlingLuckySet w)
    (hn2 : ((stirlingLuckySet w).filter (· < n)).card = 1) (i₀ iN : Fin (2 * n))
    (hi₀ : i₀.val = 0) (hiN : iN.val + 1 = n) :
    (Even n → w i₀ = 1 ∧ w iN = n ∧ (stirlingLuckySet w).card = 2) ∧
      (Odd n → w i₀ = 1 → w iN = n ∧ (stirlingLuckySet w).card = 2)

/-- The set `{1, n - 1, 2n - 2}` is `n`-admissible if and only if `n` is even,
for `n ≥ 4`. As printed the claim covers all `n`, but it fails at `n = 3`:
`w = 133221 ∈ Q_3` has `Lucky(w) = {1, 2, 4} = {1, n - 1, 2n - 2}` (spots
`1, 3, 4, 2, 5, 6`). The paper's proof assumes `n > 3`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Proposition 4.4 (`jis-2024-24.6.7-prop-35`). -/
public theorem_wanted isAdmissibleLuckySet_one_pred_two_mul_sub_two_iff (n : ℕ) (hn : 4 ≤ n) :
    IsAdmissibleLuckySet n {1, n - 1, 2 * n - 2} ↔ Even n

/-- The total displacement of `w ∈ Q_n` is invariant under permuting the entries
of `w`: `d(w ∘ σ) = d(w)` for every permutation `σ` of the positions (the
permuted word need not be a Stirling permutation).

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 5.2 (`jis-2024-24.6.7-lem-37`), quoting Elder, Harris, Kretschmann, and
Martínez Mori, Lemma 3.1. -/
public theorem_wanted stirlingTotalDisplacement_comp_perm (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (σ : Equiv.Perm (Fin (2 * n))) :
    stirlingTotalDisplacement (w ∘ σ) = stirlingTotalDisplacement w

/-- For `w ∈ Q_n`, `d(w) = n²`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 5.3 (`jis-2024-24.6.7-cor-38`). -/
public theorem_wanted stirlingTotalDisplacement_eq (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) : stirlingTotalDisplacement w = n ^ 2

/-- For `w ∈ Q_n` (`n ≥ 1`), `1 ≤ |{i ∈ [2n] : d(i) = 0}| ≤ n`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 5.6 (`jis-2024-24.6.7-cor-41`). -/
public theorem_wanted stirling_card_zero_displacement (n : ℕ) (hn : 1 ≤ n) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) :
    1 ≤ (Finset.univ.filter fun i => stirlingDisplacement w i = 0).card ∧
      (Finset.univ.filter fun i => stirlingDisplacement w i = 0).card ≤ n

/-- Let `w ∈ Q_n` be extremely lucky. For `i ∈ [n]`, the `i`-th unlucky car `j`
(the unlucky car with exactly `i - 1` unlucky cars before it) (a) prefers spot
`n - i + 1` and (b) has displacement `2i - 1`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Lemma 5.7 (`jis-2024-24.6.7-lem-42`). -/
public theorem_wanted extremely_lucky_unlucky_car (n : ℕ) (w : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (hl : (stirlingLuckySet w).card = n) (i : ℕ)
    (hi : i ∈ Finset.Icc 1 n) (j : Fin (2 * n)) (hj : j.val + 1 ∉ stirlingLuckySet w)
    (hcount : (Finset.univ.filter fun k : Fin (2 * n) =>
      k < j ∧ k.val + 1 ∉ stirlingLuckySet w).card = i - 1) :
    w j = n - i + 1 ∧ stirlingDisplacement w j = 2 * i - 1

/-- An extremely lucky `w ∈ Q_n` is determined by its displacement composition:
if `w' ∈ Q_n` has `dis(w') = dis(w)`, then `w' = w`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Theorem 5.8 (`jis-2024-24.6.7-thm-43`). -/
public theorem_wanted extremely_lucky_eq_of_displacement_eq (n : ℕ) (w w' : Fin (2 * n) → ℕ)
    (hw : IsStirlingPermutation n w) (hw' : IsStirlingPermutation n w')
    (hl : (stirlingLuckySet w).card = n)
    (hd : ∀ i, stirlingDisplacement w' i = stirlingDisplacement w i) : w' = w

/-- The number of Stirling permutations of order `n` whose displacement
composition has exactly `n` nonzero parts is the Catalan number `C_n`.

Source: L. Colmenarejo et al., *On the Lucky and Displacement Statistics of
Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7,
Corollary 5.9 (`jis-2024-24.6.7-cor-45`). -/
public theorem_wanted card_stirling_displacement_nonzero_parts (n : ℕ) :
    Nat.card {w : Fin (2 * n) → ℕ // IsStirlingPermutation n w ∧
      (Finset.univ.filter fun i => stirlingDisplacement w i ≠ 0).card = n} = catalan n

end

end MetaMathlibExt
