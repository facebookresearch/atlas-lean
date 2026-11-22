/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
public import WantedExt.Combinatorics.Enumerative.RascalNumbersWanted

namespace MetaMathlibExt

open MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted (IsAscentSeq)

@[expose] public section

/-- The number of weak ascents of a word: positions `j` with `a_j ≤ a_{j+1}`.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1 (definition of `wasc`). -/
public def wordWeakAscents : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a ≤ b then 1 else 0) + wordWeakAscents (b :: t)

/-- Weak ascent sequences: `a₁ = 0` and `aᵢ ≤ 1 + wasc(a₁ ⋯ a_{i-1})` for `i ≥ 2`
(the analogue of `IsAscentSeq` with weak ascents).

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def IsWeakAscentSeq (w : List ℕ) : Prop :=
  (∀ h : 0 < w.length, w[0]'h = 0) ∧
    ∀ (i : ℕ) (h : i < w.length), w[i]'h ≤ wordWeakAscents (w.take i) + 1

/-- Pattern containment: the word `w` contains the pattern `p` if some subsequence
of `w` of the same length as `p` is order-isomorphic to `p`.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def ContainsPattern (w p : List ℕ) : Prop :=
  ∃ s : List ℕ, s.Sublist w ∧ s.length = p.length ∧
    ∀ i < p.length, ∀ j < p.length, (s.getD i 0 < s.getD j 0 ↔ p.getD i 0 < p.getD j 0)

/-- The thirteen patterns of length three, `000, 001, 010, 011, 012, 021, 100, 101,
102, 110, 120, 201, 210`.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def lengthThreePatterns : Finset (List ℕ) :=
  {[0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 2, 1], [1, 0, 0], [1, 0, 1],
    [1, 0, 2], [1, 1, 0], [1, 2, 0], [2, 0, 1], [2, 1, 0]}

/-- The ascent sequences of length `n` avoiding every pattern in `P`, the paper's
`A_n(P)`.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def ascentAvoiders (P : Finset (List ℕ)) (n : ℕ) : Set (List ℕ) :=
  {w | w.length = n ∧ IsAscentSeq w ∧ ∀ p ∈ P, ¬ ContainsPattern w p}

/-- The weak ascent sequences of length `n` avoiding every pattern in `P`, the paper's
`WA_n(P)`.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def weakAscentAvoiders (P : Finset (List ℕ)) (n : ℕ) : Set (List ℕ) :=
  {w | w.length = n ∧ IsWeakAscentSeq w ∧ ∀ p ∈ P, ¬ ContainsPattern w p}

/-- The paper's example `00203413` has five weak ascents and is a weak ascent sequence.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public theorem isWeakAscentSeq_example :
    wordWeakAscents [0, 0, 2, 0, 3, 4, 1, 3] = 5 ∧ IsWeakAscentSeq [0, 0, 2, 0, 3, 4, 1, 3] := by
  unfold IsWeakAscentSeq
  decide

/-- The paper's example `00203413` contains the pattern `011`.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public theorem containsPattern_example : ContainsPattern [0, 0, 2, 0, 3, 4, 1, 3] [0, 1, 1] := by
  refine ⟨[0, 3, 3], by decide, rfl, ?_⟩
  decide

/-- There are thirteen patterns of length three.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public theorem card_lengthThreePatterns : lengthThreePatterns.card = 13 := by
  decide

/-- Theorem 1: the number of A-Wilf-equivalence classes among quadruples of length-3
patterns is `74`. Two sets `P`, `Q` are A-Wilf equivalent when `|A_n(P)| = |A_n(Q)|`
for every `n`, so the classes are counted as the number of distinct counting
sequences `n ↦ |A_n(P)|` over the 4-element subsets `P` of the thirteen length-3
patterns.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 1 (`integers-2025-A80-thm-1`). -/
public theorem_wanted ascent_wilf_classes_quadruples :
    ((fun P : Finset (List ℕ) => fun n : ℕ => (ascentAvoiders P n).ncard) ''
        ↑(lengthThreePatterns.powersetCard 4)).ncard = 74

/-- Theorem 2: the number of WA-Wilf-equivalence classes among quadruples of length-3
patterns is `228` or `229`, counted as the number of distinct counting sequences
`n ↦ |WA_n(P)|` over the 4-element subsets `P` of the thirteen length-3 patterns.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 2 (`integers-2025-A80-thm-2`). -/
public theorem_wanted weakAscent_wilf_classes_quadruples :
    ((fun P : Finset (List ℕ) => fun n : ℕ => (weakAscentAvoiders P n).ncard) ''
        ↑(lengthThreePatterns.powersetCard 4)).ncard = 228 ∨
      ((fun P : Finset (List ℕ) => fun n : ℕ => (weakAscentAvoiders P n).ncard) ''
        ↑(lengthThreePatterns.powersetCard 4)).ncard = 229

/-- Proposition 1: (i) the weakly increasing weak ascent sequences of length `n` are
counted by the Catalan number `C_n`; (ii) those avoiding `000` are counted by the
Motzkin number `M_n`. Stated for all `n` (at `n = 0` both sides are `1`).

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Proposition 1 (`integers-2025-A80-prop-1`). -/
public theorem_wanted weakAscent_weaklyIncreasing_card (n : ℕ) :
    {w : List ℕ | w.length = n ∧ IsWeakAscentSeq w ∧ w.Pairwise (· ≤ ·)}.ncard = catalan n ∧
      {w : List ℕ | w.length = n ∧ IsWeakAscentSeq w ∧ w.Pairwise (· ≤ ·) ∧
          ¬ ContainsPattern w [0, 0, 0]}.ncard = motzkinNumber n

/-- Theorem 5 (Class 99): `{011, 100, 102, 201}` and `{011, 100, 120, 201}` are
WA-Wilf equivalent. The extracted record drops the `w` marker on `∼`; the
weak-ascent reading follows from the class number (the paper has 74 A-classes,
and its class table numbered past 74 is the WA table).

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 5 (`integers-2025-A80-thm-5`). -/
public theorem_wanted weakAscent_wilf_class99 (n : ℕ) :
    (weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [1, 0, 2], [2, 0, 1]} n).ncard =
      (weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [1, 2, 0], [2, 0, 1]} n).ncard

/-- Theorem 7 (Class 93): `{011, 102, 120, 201}` and `{011, 102, 120, 210}` are
WA-Wilf equivalent, and `∑_{n ≥ 1} |WA_n({011, 102, 120, 201})| xⁿ =
x(2x² - 2x + 1) / ((1 - 2x)(1 - x)²)`, stated with the denominator cleared in `ℤ⟦X⟧`
(the `n = 0` term is excluded, as the generating function has no constant term).

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 7 (`integers-2025-A80-thm-7`). -/
public theorem_wanted weakAscent_wilf_class93 :
    (∀ n : ℕ, (weakAscentAvoiders {[0, 1, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1]} n).ncard =
      (weakAscentAvoiders {[0, 1, 1], [1, 0, 2], [1, 2, 0], [2, 1, 0]} n).ncard) ∧
    PowerSeries.mk (fun n : ℕ => if n = 0 then (0 : ℤ) else
        ((weakAscentAvoiders {[0, 1, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1]} n).ncard : ℤ)) *
        ((1 - 2 * PowerSeries.X) * (1 - PowerSeries.X) ^ 2) =
      PowerSeries.X * (2 * PowerSeries.X ^ 2 - 2 * PowerSeries.X + 1)

/-- Theorem 8 (Class 162): `{010, 100, 101, 120}` and `{010, 100, 110, 120}` are
WA-Wilf equivalent (weak-ascent reading as in Theorem 5).

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 8 (`integers-2025-A80-thm-8`). -/
public theorem_wanted weakAscent_wilf_class162 (n : ℕ) :
    (weakAscentAvoiders {[0, 1, 0], [1, 0, 0], [1, 0, 1], [1, 2, 0]} n).ncard =
      (weakAscentAvoiders {[0, 1, 0], [1, 0, 0], [1, 1, 0], [1, 2, 0]} n).ncard

/-- Theorem 9 (Class 205): `{100, 102, 120, 201}` and `{102, 110, 120, 201}` are
WA-Wilf equivalent (weak-ascent reading as in Theorem 5).

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 9 (`integers-2025-A80-thm-9`). -/
public theorem_wanted weakAscent_wilf_class205 (n : ℕ) :
    (weakAscentAvoiders {[1, 0, 0], [1, 0, 2], [1, 2, 0], [2, 0, 1]} n).ncard =
      (weakAscentAvoiders {[1, 0, 2], [1, 1, 0], [1, 2, 0], [2, 0, 1]} n).ncard

/-- Theorem 10 (Class 206): `{100, 102, 120, 210}`, `{101, 102, 120, 201}`,
`{101, 102, 120, 210}` and `{102, 110, 120, 210}` are WA-Wilf equivalent, stated as
equality of each count with the first.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 10 (`integers-2025-A80-thm-10`). -/
public theorem_wanted weakAscent_wilf_class206 (n : ℕ) :
    (weakAscentAvoiders {[1, 0, 0], [1, 0, 2], [1, 2, 0], [2, 1, 0]} n).ncard =
        (weakAscentAvoiders {[1, 0, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1]} n).ncard ∧
      (weakAscentAvoiders {[1, 0, 0], [1, 0, 2], [1, 2, 0], [2, 1, 0]} n).ncard =
        (weakAscentAvoiders {[1, 0, 1], [1, 0, 2], [1, 2, 0], [2, 1, 0]} n).ncard ∧
      (weakAscentAvoiders {[1, 0, 0], [1, 0, 2], [1, 2, 0], [2, 1, 0]} n).ncard =
        (weakAscentAvoiders {[1, 0, 2], [1, 1, 0], [1, 2, 0], [2, 1, 0]} n).ncard

/-- Theorem 11 (Class 219): `{100, 101, 102, 201}` and `{100, 110, 120, 201}` are
WA-Wilf equivalent (weak-ascent reading as in Theorem 5; the two sets are not
A-Wilf equivalent, their ascent-sequence counts first differ at `n = 5`: `29` versus `30`).

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 11 (`integers-2025-A80-thm-11`). -/
public theorem_wanted weakAscent_wilf_class219 (n : ℕ) :
    (weakAscentAvoiders {[1, 0, 0], [1, 0, 1], [1, 0, 2], [2, 0, 1]} n).ncard =
      (weakAscentAvoiders {[1, 0, 0], [1, 1, 0], [1, 2, 0], [2, 0, 1]} n).ncard

/-- Proposition 3, first sum: the closed form of the sum in Proposition 2(i),
`∑_{k=1}^{⌊n/3⌋-1} (C(n-k-4, 2k) 2^{n-3k-4} + C(n-k-4, 2k-1) 2^{n-3k-3}) = F_{2n-7} - 2^{n-4}`
for `n ≥ 4`, stated without subtraction as `sum + 2^{n-4} = F_{2n-7}` with the standard
Fibonacci numbers `Nat.fib`. The sum is reconstructed from the extracted display of
Proposition 2(i) (record `integers-2025-A80-prop-2`), whose tokens read, line by line, the upper
limit `⌊n/3⌋ - 1`, the summation sign, the binomial tops `n - k - 4` each followed by the
exponents `n - 3k - 4` and `n - 3k - 3`, then the bases `2 + 2`, the binomial bottoms `2k` and
`2k - 1`, and the lower limit `k = 1`; every token is used once. The primary paper is not
available to agents; exact computation confirms the identity for `4 ≤ n ≤ 500`. Truncated
subtraction in the exponent `n - 3k - 4` only matters at `n = 3k + 3`, where the
binomial factor is `0`. The second sum of Proposition 2 (over the paper's `f(n, a)`, which
the record does not define) is not stated.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Proposition 3 (`integers-2025-A80-prop-3`), with the sum of Proposition 2(i). -/
public theorem_wanted sum_choose_mul_two_pow_add_two_pow_eq_fib (n : ℕ) (hn : 4 ≤ n) :
    (∑ k ∈ Finset.Icc 1 (n / 3 - 1),
        (Nat.choose (n - k - 4) (2 * k) * 2 ^ (n - 3 * k - 4) +
          Nat.choose (n - k - 4) (2 * k - 1) * 2 ^ (n - 3 * k - 3))) + 2 ^ (n - 4) =
      Nat.fib (2 * n - 7)

/-- Theorem 3 (reducible pattern sets, from the paper's reference [5]): for each listed pair
`C ⊊ B`, `C ∼r B`, i.e. `A_n(B) = A_n(C)` and `WA_n(B) = WA_n(C)` for all `n`. The paper's
Step 3 defines `∼r` in both the ascent and the weak-ascent case and uses Theorem 3 for both
tables; both readings are stated. The items "for any `τ = …`" are expanded into one pair per
`τ`, giving 36 pairs.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 3 (`integers-2025-A80-thm-3`). -/
public theorem_wanted reducible_pattern_sets :
    ∀ CB ∈ ([
      ({[0, 0, 1]}, {[0, 0, 1], [1, 0, 1]}), ({[0, 0, 1]}, {[0, 0, 1], [1, 0, 2]}),
      ({[0, 0, 1]}, {[0, 0, 1], [2, 0, 1]}), ({[0, 1, 1]}, {[0, 1, 1], [1, 0, 1]}),
      ({[0, 1, 1]}, {[0, 1, 1], [1, 1, 0]}), ({[0, 1, 2]}, {[0, 1, 2], [1, 0, 2]}),
      ({[0, 1, 2]}, {[0, 1, 2], [1, 2, 0]}), ({[0, 2, 1]}, {[0, 2, 1], [2, 0, 1]}),
      ({[0, 2, 1]}, {[0, 2, 1], [2, 1, 0]}),
      ({[0, 0, 0], [0, 0, 1]}, {[0, 0, 0], [0, 0, 1], [1, 0, 0]}),
      ({[0, 0, 0], [0, 1, 1]}, {[0, 0, 0], [0, 1, 1], [1, 0, 0]}),
      ({[0, 0, 0], [0, 1, 1]}, {[0, 0, 0], [0, 1, 1], [2, 0, 1]}),
      ({[0, 0, 0], [0, 1, 1]}, {[0, 0, 0], [0, 1, 1], [2, 1, 0]}),
      ({[0, 0, 0], [0, 1, 2]}, {[0, 0, 0], [0, 1, 2], [2, 0, 1]}),
      ({[0, 0, 0], [0, 1, 2]}, {[0, 0, 0], [0, 1, 2], [2, 1, 0]}),
      ({[0, 0, 0], [0, 2, 1]}, {[0, 0, 0], [0, 2, 1], [1, 0, 0]}),
      ({[0, 0, 1], [0, 1, 0]}, {[0, 0, 1], [0, 1, 0], [0, 2, 1]}),
      ({[0, 0, 1], [0, 1, 0]}, {[0, 0, 1], [0, 1, 0], [1, 0, 0]}),
      ({[0, 0, 1], [0, 1, 0]}, {[0, 0, 1], [0, 1, 0], [1, 1, 0]}),
      ({[0, 0, 1], [0, 1, 0]}, {[0, 0, 1], [0, 1, 0], [1, 2, 0]}),
      ({[0, 0, 1], [0, 1, 0]}, {[0, 0, 1], [0, 1, 0], [2, 1, 0]}),
      ({[0, 0, 1], [0, 1, 1]}, {[0, 0, 1], [0, 1, 1], [0, 2, 1]}),
      ({[0, 0, 1], [0, 1, 2]}, {[0, 0, 1], [0, 1, 2], [0, 2, 1]}),
      ({[0, 0, 1], [1, 1, 0]}, {[0, 0, 1], [1, 1, 0], [2, 1, 0]}),
      ({[0, 0, 1], [1, 2, 0]}, {[0, 0, 1], [1, 2, 0], [2, 1, 0]}),
      ({[0, 1, 0], [0, 1, 1]}, {[0, 1, 0], [0, 1, 1], [1, 0, 0]}),
      ({[0, 1, 0], [0, 1, 2]}, {[0, 1, 0], [0, 1, 2], [1, 0, 1]}),
      ({[0, 1, 0], [0, 1, 2]}, {[0, 1, 0], [0, 1, 2], [2, 0, 1]}),
      ({[0, 1, 0], [0, 2, 1]}, {[0, 1, 0], [0, 2, 1], [1, 0, 0]}),
      ({[0, 1, 0], [0, 2, 1]}, {[0, 1, 0], [0, 2, 1], [1, 0, 1]}),
      ({[0, 1, 0], [0, 2, 1]}, {[0, 1, 0], [0, 2, 1], [1, 0, 2]}),
      ({[0, 1, 0], [0, 2, 1]}, {[0, 1, 0], [0, 2, 1], [1, 1, 0]}),
      ({[0, 1, 0], [0, 2, 1]}, {[0, 1, 0], [0, 2, 1], [1, 2, 0]}),
      ({[0, 0, 1], [0, 1, 1], [0, 1, 2]}, {[0, 0, 1], [0, 1, 1], [0, 1, 2], [2, 1, 0]}),
      ({[0, 0, 1], [0, 1, 1], [1, 0, 0]}, {[0, 0, 1], [0, 1, 1], [1, 0, 0], [2, 1, 0]}),
      ({[0, 0, 1], [0, 1, 2], [1, 0, 0]}, {[0, 0, 1], [0, 1, 2], [1, 0, 0], [2, 1, 0]})] :
        List (Finset (List ℕ) × Finset (List ℕ))),
      ∀ n : ℕ, ascentAvoiders CB.2 n = ascentAvoiders CB.1 n ∧
        weakAscentAvoiders CB.2 n = weakAscentAvoiders CB.1 n

/-- Theorem 4 (Class 86): for `P = {000, 021, 101, 120}`, `Q = {000, 021, 101, 102}` and
`R = {000, 021, 110, 120}`, `|WA_n(P)| = |WA_n(Q)| = |WA_n(R)| = M_n + M_{n-2}` for `n ≥ 3`,
with `M_n` the Motzkin numbers.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 4 (`integers-2025-A80-thm-4`). -/
public theorem_wanted weakAscent_class86_card_eq_motzkin (n : ℕ) (hn : 3 ≤ n) :
    (weakAscentAvoiders {[0, 0, 0], [0, 2, 1], [1, 0, 1], [1, 2, 0]} n).ncard =
        motzkinNumber n + motzkinNumber (n - 2) ∧
      (weakAscentAvoiders {[0, 0, 0], [0, 2, 1], [1, 0, 1], [1, 0, 2]} n).ncard =
        motzkinNumber n + motzkinNumber (n - 2) ∧
      (weakAscentAvoiders {[0, 0, 0], [0, 2, 1], [1, 1, 0], [1, 2, 0]} n).ncard =
        motzkinNumber n + motzkinNumber (n - 2)

/-- Theorem 6 (Class 61): `{010, 011, 102, 201}` and `{010, 011, 120, 201}` are WA-Wilf
equivalent (the paper writes `∼` with the `w` marker).

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 6 (`integers-2025-A80-thm-6`). -/
public theorem_wanted weakAscent_wilf_class61 (n : ℕ) :
    (weakAscentAvoiders {[0, 1, 0], [0, 1, 1], [1, 0, 2], [2, 0, 1]} n).ncard =
      (weakAscentAvoiders {[0, 1, 0], [0, 1, 1], [1, 2, 0], [2, 0, 1]} n).ncard

/-- Theorem 12 (Class 211): for `Q = {101, 102, 110, 201}` and
`F(x) = ∑_{n ≥ 0} |WA_n(Q)| xⁿ`,
`F(x) = ((2 - 3x - x²) √(1 - 4x) - x - x²) / (2(1 - x)(1 - 4x - x²))`, stated in `ℚ⟦X⟧` with
the denominator cleared and `√(1 - 4x)` as any power series `S` with `S² = 1 - 4X` and constant
term `1`.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 12 (`integers-2025-A80-thm-12`). -/
public theorem_wanted weakAscent_class211_generatingFunction (S : PowerSeries ℚ)
    (hS : S ^ 2 = 1 - 4 * PowerSeries.X) (hS0 : PowerSeries.constantCoeff S = 1) :
    PowerSeries.mk (fun n : ℕ =>
        ((weakAscentAvoiders {[1, 0, 1], [1, 0, 2], [1, 1, 0], [2, 0, 1]} n).ncard : ℚ)) *
        (2 * (1 - PowerSeries.X) * (1 - 4 * PowerSeries.X - PowerSeries.X ^ 2)) =
      (2 - 3 * PowerSeries.X - PowerSeries.X ^ 2) * S - PowerSeries.X - PowerSeries.X ^ 2

/-- A big entry of a weak ascent sequence: the entry `w_k` (`k ≥ 2`, one-indexed; here the
zero-based index `i = k - 1 ≥ 1`) equal to `1` plus the number of weak ascents of
`w_1 ⋯ w_{k-1}`, i.e. the largest value allowed at that position.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3
(definition of big entry). -/
public def IsBigEntry (w : List ℕ) (i : ℕ) : Prop :=
  1 ≤ i ∧ i < w.length ∧ w.getD i 0 = wordWeakAscents (w.take i) + 1

public instance (w : List ℕ) (i : ℕ) : Decidable (IsBigEntry w i) := by
  unfold IsBigEntry; infer_instance

/-- In `00203413` the entries `2` (position 3) and `4` (position 6) are big, and the `1` at
position 7 is not.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3. -/
public theorem isBigEntry_example :
    IsBigEntry [0, 0, 2, 0, 3, 4, 1, 3] 2 ∧ IsBigEntry [0, 0, 2, 0, 3, 4, 1, 3] 5 ∧
      ¬ IsBigEntry [0, 0, 2, 0, 3, 4, 1, 3] 6 := by
  decide

/-- The (one-indexed) position of the last descent top of `w`, or `0` if `w` has no descent.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3
(definition of `W_{n,k}`). -/
public def lastDescentTop (w : List ℕ) : ℕ :=
  ((Finset.range (w.length - 1)).filter fun i => w.getD (i + 1) 0 < w.getD i 0).sup (· + 1)

/-- The last descent top of each of `0010, 0020, 0021, 0120` (the paper's `W_{4,3}`) is at
position `3`; `012` has no descent.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3. -/
public theorem lastDescentTop_example :
    lastDescentTop [0, 0, 1, 0] = 3 ∧ lastDescentTop [0, 0, 2, 0] = 3 ∧
      lastDescentTop [0, 0, 2, 1] = 3 ∧ lastDescentTop [0, 1, 2, 0] = 3 ∧
      lastDescentTop [0, 1, 2] = 0 := by
  decide

/-- `U_{n,j}`: the sequences `w ∈ W_n = WA_n(011, 100, 201, 210)` whose last descent top is at
position `n - 1`, with a big entry, first `n - 2` entries not all `0`, `w_{n-1} ≠ n - 2` and
`w_{n-1} - w_n = j` (one-indexed entries; `w_k` is `w.getD (k - 1) 0`).

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3.2
(definition of `U_{n,j}`). -/
public def quadrupleUSet (n j : ℕ) : Set (List ℕ) :=
  {w | w ∈ weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} n ∧
    lastDescentTop w = n - 1 ∧ (∃ i < n, IsBigEntry w i) ∧ (∃ i < n - 2, w.getD i 0 ≠ 0) ∧
    w.getD (n - 2) 0 ≠ n - 2 ∧ w.getD (n - 2) 0 = w.getD (n - 1) 0 + j}

/-- `U_{0,j} = ∅`.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3.2. -/
public theorem quadrupleUSet_zero (j : ℕ) : quadrupleUSet 0 j = ∅ := by
  ext w
  simp [quadrupleUSet]

/-- `V_{n,j}`: the sequences `w ∈ W_n` whose last descent top is at position `n - 2`, with
`w_n ≤ n - 3`, `w_{n-1} ≠ 0` and `w_{n-2} - w_{n-1} = j` (one-indexed entries).

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3.2
(definition of `V_{n,j}`). -/
public def quadrupleVSet (n j : ℕ) : Set (List ℕ) :=
  {w | w ∈ weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} n ∧
    lastDescentTop w = n - 2 ∧ w.getD (n - 1) 0 ≤ n - 3 ∧ w.getD (n - 2) 0 ≠ 0 ∧
    w.getD (n - 3) 0 = w.getD (n - 2) 0 + j}

/-- `V_{n,j} ⊆ W_n`.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3.2. -/
public theorem quadrupleVSet_subset (n j : ℕ) :
    quadrupleVSet n j ⊆ weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} n :=
  fun _ h => h.1

/-- Lemma 1: for `w ∈ W_n = WA_n(011, 100, 201, 210)` and `2 ≤ k ≤ n - 1`, if `w_k` is a big
entry then either `w_{k+1}` is a big entry, or `w_k, w_{k+1}` is a descent pair and `w_j` is a
big entry for every `k + 2 ≤ j ≤ n` (one-indexed `w_k` at zero-based index `k - 1`).

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Lemma 1 (`integers-2025-A80-lem-1`). -/
public theorem_wanted isBigEntry_succ_or_descent (n : ℕ) (w : List ℕ)
    (hw : w ∈ weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} n) (k : ℕ)
    (hk : 2 ≤ k) (hkn : k ≤ n - 1) (hbig : IsBigEntry w (k - 1)) :
    IsBigEntry w k ∨
      (w.getD k 0 < w.getD (k - 1) 0 ∧ ∀ j, k + 2 ≤ j → j ≤ n → IsBigEntry w (j - 1))

/-- Lemma 2: `u_n = |U_{n,1}|` and `v_n = |V_{n,1}|` both satisfy
`f_n = 5 f_{n-1} - 7 f_{n-2} + 2 f_{n-3}` (for `n ≥ 7`, stated in `ℤ`) with `f_6 = 1` and
`f_j = 0` for all `j ≤ 5`.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Lemma 2 (`integers-2025-A80-lem-2`). -/
public theorem_wanted quadrupleUSet_quadrupleVSet_recurrence :
    ∀ f ∈ [fun n => (quadrupleUSet n 1).ncard, fun n => (quadrupleVSet n 1).ncard],
      (∀ j ≤ 5, f j = 0) ∧ f 6 = 1 ∧
        ∀ n, 7 ≤ n → (f n : ℤ) = 5 * f (n - 1) - 7 * f (n - 2) + 2 * f (n - 3)

/-- Proposition 2: for `n ≥ 1`, (i)
`|U_{n,1}| = ∑_{k=1}^{⌊n/3⌋-1} (C(n-k-4, 2k) 2^{n-3k-4} + C(n-k-4, 2k-1) 2^{n-3k-3})`, and
(ii) with `f(n, a) = min(n - 3 - a, ⌊(a - 1)/2⌋)`,
`|V_{n,1}| = ∑_{a=2}^{n-4} 2^{a-2}(n - a - 3) + ∑_{a=2}^{n-4} ∑_{k=1}^{f(n,a)}
(C(a-2, 2k) 2^{a-2k-2} + C(a-2, 2k-1) 2^{a-2k-1})(n - k - a - 2)`. Natural-number exponents
truncate only where the binomial factor vanishes. The paper's second form of (ii), with
`∑_{a=2}^{n-4} 2^{a-2}(n - a - 3) = 2^{n-4} - n + 3`, is stated in `ℤ` for `n ≥ 4`: for
`n ≤ 3`, `2^{n-4} - n + 3` is not an integer (`1/2` at `n = 3`) while the sum is `0`.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Proposition 2 (`integers-2025-A80-prop-2`). -/
public theorem_wanted quadrupleUSet_quadrupleVSet_card_formulas :
    (∀ n : ℕ, 1 ≤ n →
      (quadrupleUSet n 1).ncard =
        ∑ k ∈ Finset.Icc 1 (n / 3 - 1),
          (Nat.choose (n - k - 4) (2 * k) * 2 ^ (n - 3 * k - 4) +
            Nat.choose (n - k - 4) (2 * k - 1) * 2 ^ (n - 3 * k - 3))) ∧
    (∀ n : ℕ, 1 ≤ n →
      (quadrupleVSet n 1).ncard =
        ∑ a ∈ Finset.Icc 2 (n - 4), 2 ^ (a - 2) * (n - a - 3) +
          ∑ a ∈ Finset.Icc 2 (n - 4), ∑ k ∈ Finset.Icc 1 (min (n - 3 - a) ((a - 1) / 2)),
            (Nat.choose (a - 2) (2 * k) * 2 ^ (a - 2 * k - 2) +
              Nat.choose (a - 2) (2 * k - 1) * 2 ^ (a - 2 * k - 1)) * (n - k - a - 2)) ∧
    ∀ n : ℕ, 4 ≤ n →
      ((quadrupleVSet n 1).ncard : ℤ) =
        2 ^ (n - 4) - n + 3 +
          ∑ a ∈ Finset.Icc 2 (n - 4), ∑ k ∈ Finset.Icc 1 (min (n - 3 - a) ((a - 1) / 2)),
            ((Nat.choose (a - 2) (2 * k) * 2 ^ (a - 2 * k - 2) +
              Nat.choose (a - 2) (2 * k - 1) * 2 ^ (a - 2 * k - 1)) * (n - k - a - 2) : ℕ)

end

end MetaMathlibExt
