/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Order.Lattice.Nat

/-!
# Four-digit Kaprekar dynamics in odd bases (Chen, Ono, Schwartz, Thakur)

Cycle-length and cycle-count statements from E. Chen, K. Ono, R. E. Schwartz and
D. Thakur, *Four-Digit Kaprekar Dynamics in Odd Bases*, Journal of Integer Sequences
29 (2026), Article 26.4.7.

The Kaprekar routine on a four-digit base-`B` string with sorted digits
`a₁ ≥ a₂ ≥ a₃ ≥ a₄` depends only on the difference pair `(d₁, d₂) = (a₁ - a₄, a₂ - a₃)`;
the paper works on the state space `X_B = {(d₁, d₂) : 1 ≤ d₁ < B, 0 ≤ d₂ ≤ d₁}` (constant
strings omitted) and counts terminal cycles of the induced map `K_B` there. A terminal
cycle of length `L` is a periodic orbit of `K_B` in `X_B` of minimal period `L`, so the
number of such cycles is the number of points of minimal period `L` divided by `L`.

The structural classification (Theorem 1, with Lemma 11, Lemma 14 and Proposition 16)
is already proved as `MetaMathlibExt.four_digit_kaprekar_structural_classification` in
`MathlibExt/NumberTheory/Digits/KaprekarStructuralClassification.lean`, whose
`let`-bound map `kaprekar` is the same formula as `kaprekarFourDigitStep` below.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The four-digit Kaprekar map `K_B` in difference coordinates: for `d₂ > 0` the unsorted
output digits are `[d₁, d₂ - 1, B - d₂ - 1, B - d₁]`, for `d₂ = 0` they are
`[d₁ - 1, B - 1, B - 1, B - d₁]` (paper displays (5) and (6)); sort them decreasingly and
take the outer and inner differences.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Section 2.1. -/
public def kaprekarFourDigitStep (B : ℕ) (d : ℕ × ℕ) : ℕ × ℕ :=
  match List.insertionSort (· ≥ ·)
    (if d.2 = 0 then [d.1 - 1, B - 1, B - 1, B - d.1]
      else [d.1, d.2 - 1, B - d.2 - 1, B - d.1]) with
  | [a, b, c, e] => (a - e, b - c)
  | _ => (0, 0)

/-- Characteristic values: in base `11`, `(5, 1) ↦ (9, 1)` and `(6, 0) ↦ (5, 5) ↦ (2, 0)`;
in base `7`, the terminal cycle `(3, 1) ↦ (5, 1) ↦ (5, 3) ↦ (3, 1)`.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Examples 7, 12 and 18. -/
public theorem kaprekarFourDigitStep_examples :
    kaprekarFourDigitStep 11 (5, 1) = (9, 1) ∧ kaprekarFourDigitStep 11 (6, 0) = (5, 5) ∧
      kaprekarFourDigitStep 11 (5, 5) = (2, 0) ∧ kaprekarFourDigitStep 7 (3, 1) = (5, 1) ∧
      kaprekarFourDigitStep 7 (5, 1) = (5, 3) ∧ kaprekarFourDigitStep 7 (5, 3) = (3, 1) := by
  simp [kaprekarFourDigitStep, List.insertionSort_cons, List.orderedInsert_cons]

/-- The state space `X_B = {(d₁, d₂) : 1 ≤ d₁ < B, 0 ≤ d₂ ≤ d₁}` of nonconstant four-digit
strings in difference coordinates.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
display (2). -/
public def kaprekarFourDigitStates (B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range B ×ˢ Finset.range B).filter fun d => 1 ≤ d.1 ∧ d.2 ≤ d.1

/-- Characteristic values: `|X_3| = 5` and `|X_7| = 27`, i.e. `(B - 1)(B + 2) / 2`.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
display (2) and the proof of Corollary 27. -/
public theorem kaprekarFourDigitStates_card_examples :
    (kaprekarFourDigitStates 3).card = 5 ∧ (kaprekarFourDigitStates 7).card = 27 := by
  decide

/-- The projective order of `2` modulo `n`, `λ(n) = min {m > 0 : 2 ^ m ≡ ±1 (mod n)}`
(OEIS A003558); defined as `0` when no such `m` exists, which happens exactly for even `n`
(including `n = 0` and `n = 2`).

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Definition 19, display (13). -/
public noncomputable def projectiveOrderTwo (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ((2 : ZMod n) ^ m = 1 ∨ (2 : ZMod n) ^ m = -1)}

/-- Characterization of `λ(n)`: the least positive `m` with `2 ^ m ≡ ±1 (mod n)`.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Definition 19, display (13). -/
public theorem projectiveOrderTwo_eq_of {n m : ℕ} (hm : 0 < m)
    (h : (2 : ZMod n) ^ m = 1 ∨ (2 : ZMod n) ^ m = -1)
    (hmin : ∀ k < m, 0 < k → (2 : ZMod n) ^ k ≠ 1 ∧ (2 : ZMod n) ^ k ≠ -1) :
    projectiveOrderTwo n = m := by
  unfold projectiveOrderTwo
  refine le_antisymm (Nat.sInf_le ⟨hm, h⟩) (le_csInf ⟨m, hm, h⟩ ?_)
  rintro k ⟨hk, hk2⟩
  by_contra hlt
  have hne := hmin k (lt_of_not_ge hlt) hk
  rcases hk2 with h' | h'
  · exact hne.1 h'
  · exact hne.2 h'

/-- Characteristic values: `λ(7) = 3`, `λ(9) = 3`, `λ(11) = 5`, `λ(17) = 4`.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Examples 7-10 and 23. -/
public theorem projectiveOrderTwo_examples :
    projectiveOrderTwo 7 = 3 ∧ projectiveOrderTwo 9 = 3 ∧ projectiveOrderTwo 11 = 5 ∧
      projectiveOrderTwo 17 = 4 :=
  ⟨projectiveOrderTwo_eq_of (by omega) (by decide) (by decide),
    projectiveOrderTwo_eq_of (by omega) (by decide) (by decide),
    projectiveOrderTwo_eq_of (by omega) (by decide) (by decide),
    projectiveOrderTwo_eq_of (by omega) (by decide) (by decide)⟩

/-- Every cycle of the doubling map `{[r], [s]} ↦ {[2r], [2s]}` on unordered pairs of
distinct nonzero projective classes modulo `B` has length at most `λ(B)`. A class
`[x] = {x, -x}` is a `Finset (ZMod B)` and a pair is a two-element set of classes, as in
`four_digit_kaprekar_structural_classification`; every such pair is periodic and its
minimal period is at most `λ(B)`.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7, Lemma 20
(`jis-2026-26.4.7-lem-20`). -/
public theorem_wanted projective_doubling_minimalPeriod_le_projectiveOrderTwo (B : ℕ)
    (hB : Odd B) (hB3 : 3 < B) (S : Finset (Finset (ZMod B)))
    (hS : S.card = 2 ∧ ∀ C ∈ S, ∃ x : ZMod B, x ≠ 0 ∧ C = {x, -x}) :
    0 < Function.minimalPeriod
        (fun T : Finset (Finset (ZMod B)) => T.image fun C => C.image (· * 2)) S ∧
      Function.minimalPeriod
        (fun T : Finset (Finset (ZMod B)) => T.image fun C => C.image (· * 2)) S ≤
        projectiveOrderTwo B

/-- For odd `B > 3`, `λ(B) ≤ φ(B) / 2`.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7, Lemma 21
(quoting Kay and Downes-Ward, Theorem 2) (`jis-2026-26.4.7-lem-21`). -/
public theorem_wanted projectiveOrderTwo_le_totient_div_two (B : ℕ) (hB : Odd B)
    (hB3 : 3 < B) :
    projectiveOrderTwo B ≤ B.totient / 2

/-- For odd `B > 3`, every terminal cycle of `K_B` on `X_B` has length at most
`(B - 1) / 2`, and if some terminal cycle has length `(B - 1) / 2` then `B` is prime.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 22 (`jis-2026-26.4.7-cor-22`). -/
public theorem_wanted kaprekar_minimalPeriod_le_and_prime_of_eq (B : ℕ) (hB : Odd B)
    (hB3 : 3 < B) :
    (∀ d ∈ kaprekarFourDigitStates B, d ∈ Function.periodicPts (kaprekarFourDigitStep B) →
      Function.minimalPeriod (kaprekarFourDigitStep B) d ≤ (B - 1) / 2) ∧
      ((∃ d ∈ kaprekarFourDigitStates B,
          Function.minimalPeriod (kaprekarFourDigitStep B) d = (B - 1) / 2) → B.Prime)

/-- Cycle-length bound: for odd `B > 3`, every terminal cycle of `K_B` on `X_B` has length
at most `(B - 1) / 2`, and some terminal cycle has length `(B - 1) / 2` (i.e.
`c_max(B) = (B - 1) / 2`) if and only if `B ≥ 7`, `B` is prime and `λ(B) = (B - 1) / 2`.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 3 (`jis-2026-26.4.7-cor-3`). -/
public theorem_wanted kaprekar_minimalPeriod_le_and_eq_iff (B : ℕ) (hB : Odd B)
    (hB3 : 3 < B) :
    (∀ d ∈ kaprekarFourDigitStates B, d ∈ Function.periodicPts (kaprekarFourDigitStep B) →
      Function.minimalPeriod (kaprekarFourDigitStep B) d ≤ (B - 1) / 2) ∧
      ((∃ d ∈ kaprekarFourDigitStates B,
          Function.minimalPeriod (kaprekarFourDigitStep B) d = (B - 1) / 2) ↔
        7 ≤ B ∧ B.Prime ∧ projectiveOrderTwo B = (B - 1) / 2)

/-- Prime bases and maximal cycles: for odd `B > 3` with a terminal cycle of length
`q = (B - 1) / 2 = c_max(B)`, there are exactly `⌊(q - 1) / 2⌋` terminal cycles of length
`q`; stated as: the points of `X_B` of minimal period `q` number `q · ⌊(q - 1) / 2⌋`.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 5 (`jis-2026-26.4.7-cor-5`). -/
public theorem_wanted kaprekar_card_maximal_cycles (B : ℕ) (hB : Odd B) (hB3 : 3 < B)
    (heq : ∃ d ∈ kaprekarFourDigitStates B,
      Function.minimalPeriod (kaprekarFourDigitStep B) d = (B - 1) / 2) :
    ((kaprekarFourDigitStates B).filter fun d =>
        Function.minimalPeriod (kaprekarFourDigitStep B) d = (B - 1) / 2).card =
      (B - 1) / 2 * (((B - 1) / 2 - 1) / 2)

/-- Explicit cycle counts: for odd `B > 3` and `L ≥ 1`, the number `N_B(L)` of terminal
cycles of length `L` of `K_B` on `X_B` is
`μ_B(L) ⌊(L - 1)/2⌋ + μ_B(2L) + C(μ_B(L), 2) L + ∑_{a < b, lcm(a, b) = L} μ_B(a) μ_B(b) gcd(a, b)`,
where `μ_B(a) = ∑_{n ∣ B, n > 1, λ(n) = a} φ(n) / (2a)`; stated as: the points of `X_B`
of minimal period `L` number `L · N_B(L)`. In the sum, `a` and `b` range over divisors
of `L` (forced by `lcm(a, b) = L`).

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Theorem 24, with `μ_B` from display (14) (`jis-2026-26.4.7-thm-24`). -/
public theorem_wanted kaprekar_card_minimalPeriod_eq (B : ℕ) (hB : Odd B) (hB3 : 3 < B)
    (L : ℕ) (hL : 0 < L) :
    let μ : ℕ → ℕ := fun a =>
      ∑ n ∈ B.divisors with 1 < n ∧ projectiveOrderTwo n = a, n.totient / (2 * a)
    ((kaprekarFourDigitStates B).filter fun d =>
        Function.minimalPeriod (kaprekarFourDigitStep B) d = L).card =
      L * (μ L * ((L - 1) / 2) + μ (2 * L) + (μ L).choose 2 * L +
        ∑ p ∈ (L.divisors ×ˢ L.divisors).filter (fun p => p.1 < p.2 ∧ Nat.lcm p.1 p.2 = L),
          μ p.1 * μ p.2 * Nat.gcd p.1 p.2)

/-- For odd `B > 17` there are at least two terminal cycles of `K_B` of length `λ(B)`;
stated as: at least `2 λ(B)` points of `X_B` have minimal period `λ(B)`.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 27 (i) (`jis-2026-26.4.7-cor-27`). -/
public theorem_wanted two_mul_projectiveOrderTwo_le_card_kaprekar_cycles (B : ℕ)
    (hB : Odd B) (hB3 : 17 < B) :
    2 * projectiveOrderTwo B ≤
      ((kaprekarFourDigitStates B).filter fun d =>
        Function.minimalPeriod (kaprekarFourDigitStep B) d = projectiveOrderTwo B).card

/-- For odd `B ≥ 3`, `K_B` has a unique terminal cycle on `X_B` (some periodic point `c`
whose orbit contains every periodic point of `X_B`) if and only if `B ∈ {3, 5, 7}`.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Corollary 27 (ii) (`jis-2026-26.4.7-cor-27`). -/
public theorem_wanted kaprekar_unique_cycle_iff (B : ℕ) (hB : Odd B) (hB3 : 3 ≤ B) :
    (∃ c ∈ kaprekarFourDigitStates B, c ∈ Function.periodicPts (kaprekarFourDigitStep B) ∧
      ∀ d ∈ kaprekarFourDigitStates B, d ∈ Function.periodicPts (kaprekarFourDigitStep B) →
        ∃ k, (kaprekarFourDigitStep B)^[k] c = d) ↔
      B = 3 ∨ B = 5 ∨ B = 7

end

end MetaMathlibExt
