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

/-- **Number of weak ascents of a word.** For a word $a_1 a_2 \cdots a_m$ of natural numbers,
$\mathrm{wasc}(a_1 \cdots a_m)$ is the number of weak ascents, that is, of positions $j$ with
$1 \le j < m$ and $a_j \le a_{j+1}$; in particular the empty word and every word of length one
have no weak ascents.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1 (definition of `wasc`). -/
public def wordWeakAscents : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a ≤ b then 1 else 0) + wordWeakAscents (b :: t)

/-- **Weak ascent sequence.** A word $a_1 a_2 \cdots a_n$ over $\mathbb{N}$ is a weak ascent
sequence if either $n = 0$, or $a_1 = 0$ and $a_i \le 1 + \operatorname{wasc}(a_1 \cdots a_{i-1})$
for every $2 \le i \le n$, where $\operatorname{wasc}(u)$ is the number of weak ascents of $u$,
that is, of positions $j$ with $u_j \le u_{j+1}$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def IsWeakAscentSeq (w : List ℕ) : Prop :=
  (∀ h : 0 < w.length, w[0]'h = 0) ∧
    ∀ (i : ℕ) (h : i < w.length), w[i]'h ≤ wordWeakAscents (w.take i) + 1

/-- **Pattern containment in words.** A word $w$ over $\mathbb{N}$ contains a pattern $p$ (another
word over $\mathbb{N}$) if $w$ has a subsequence $s$, not necessarily contiguous, of the same
length as $p$ that is order-isomorphic to $p$: for all positions $i$ and $j$, $s_i < s_j$ if and
only if $p_i < p_j$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def ContainsPattern (w p : List ℕ) : Prop :=
  ∃ s : List ℕ, s.Sublist w ∧ s.length = p.length ∧
    ∀ i < p.length, ∀ j < p.length, (s.getD i 0 < s.getD j 0 ↔ p.getD i 0 < p.getD j 0)

/-- **The thirteen patterns of length three.** The set of patterns of length three consists of
the thirteen words $000$, $001$, $010$, $011$, $012$, $021$, $100$, $101$, $102$, $110$, $120$,
$201$ and $210$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def lengthThreePatterns : Finset (List ℕ) :=
  {[0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 2, 1], [1, 0, 0], [1, 0, 1],
    [1, 0, 2], [1, 1, 0], [1, 2, 0], [2, 0, 1], [2, 1, 0]}

/-- **Ascent sequences avoiding a set of patterns.** For a finite set $P$ of patterns (words over
$\mathbb{N}$) and $n \in \mathbb{N}$, $A_n(P)$ is the set of ascent sequences of length $n$ that
contain no pattern of $P$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def ascentAvoiders (P : Finset (List ℕ)) (n : ℕ) : Set (List ℕ) :=
  {w | w.length = n ∧ IsAscentSeq w ∧ ∀ p ∈ P, ¬ ContainsPattern w p}

/-- **Weak ascent sequences avoiding a set of patterns.** For a finite set $P$ of patterns
(words over $\mathbb{N}$) and a natural number $n$, $\mathrm{WA}_n(P)$ is the set of weak ascent
sequences of length $n$ that contain none of the patterns in $P$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def weakAscentAvoiders (P : Finset (List ℕ)) (n : ℕ) : Set (List ℕ) :=
  {w | w.length = n ∧ IsWeakAscentSeq w ∧ ∀ p ∈ P, ¬ ContainsPattern w p}

/-- **The weak ascent sequence $00203413$.** The word $00203413$ has five weak ascents and is a
weak ascent sequence.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public theorem isWeakAscentSeq_example :
    wordWeakAscents [0, 0, 2, 0, 3, 4, 1, 3] = 5 ∧ IsWeakAscentSeq [0, 0, 2, 0, 3, 4, 1, 3] := by
  unfold IsWeakAscentSeq
  decide

/-- **The word $00203413$ contains $011$.** The word $00203413$ contains the pattern $011$.

For example, its subsequence $033$ is order-isomorphic to $011$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public theorem containsPattern_example : ContainsPattern [0, 0, 2, 0, 3, 4, 1, 3] [0, 1, 1] := by
  refine ⟨[0, 3, 3], by decide, rfl, ?_⟩
  decide

/-- **Number of patterns of length three.** The set of patterns of length three,
$\{000, 001, 010, 011, 012, 021, 100, 101, 102, 110, 120, 201, 210\}$, has exactly $13$ elements.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public theorem card_lengthThreePatterns : lengthThreePatterns.card = 13 := by
  decide

/-- **Number of Wilf classes of ascent sequences avoiding four length-3 patterns.** For a set $P$
of patterns, let $A_n(P)$ be the set of ascent sequences of length $n$ avoiding every pattern in
$P$. As $P$ ranges over the $4$-element subsets of the thirteen patterns of length three, the
counting sequences $n \mapsto |A_n(P)|$ take exactly $74$ distinct values. Equivalently, there are
$74$ A-Wilf-equivalence classes of such quadruples, where $P$ and $Q$ are A-Wilf equivalent when
$|A_n(P)| = |A_n(Q)|$ for every $n \ge 0$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 1 (`integers-2025-A80-thm-1`). -/
public theorem_wanted ascent_wilf_classes_quadruples :
    ((fun P : Finset (List ℕ) => fun n : ℕ => (ascentAvoiders P n).ncard) ''
        ↑(lengthThreePatterns.powersetCard 4)).ncard = 74

/-- **WA-Wilf classes of pattern quadruples.** Write $\mathrm{WA}_n(P)$ for the set of weak ascent
sequences of length $n$ avoiding every pattern in $P$, and call two sets of patterns $P$ and $Q$
WA-Wilf equivalent when $|\mathrm{WA}_n(P)| = |\mathrm{WA}_n(Q)|$ for every $n \ge 0$. As $P$
ranges over the $4$-element subsets of the thirteen patterns of length three, the counting
sequences $n \mapsto |\mathrm{WA}_n(P)|$ take exactly $228$ or exactly $229$ distinct values;
that is, there are $228$ or $229$ WA-Wilf equivalence classes of such quadruples.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 2 (`integers-2025-A80-thm-2`). -/
public theorem_wanted weakAscent_wilf_classes_quadruples :
    ((fun P : Finset (List ℕ) => fun n : ℕ => (weakAscentAvoiders P n).ncard) ''
        ↑(lengthThreePatterns.powersetCard 4)).ncard = 228 ∨
      ((fun P : Finset (List ℕ) => fun n : ℕ => (weakAscentAvoiders P n).ncard) ''
        ↑(lengthThreePatterns.powersetCard 4)).ncard = 229

/-- **Weakly increasing weak ascent sequences: Catalan and Motzkin counts.** Let $C_n$ denote the
Catalan numbers and $M_n$ the Motzkin numbers. For every natural number $n$, (i) the number of
weakly increasing weak ascent sequences of length $n$ is $C_n$, and (ii) the number of weakly
increasing weak ascent sequences of length $n$ that avoid the pattern $000$ is $M_n$.

At $n = 0$ both counts are $1$, from the empty sequence.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Proposition 1 (`integers-2025-A80-prop-1`). -/
public theorem_wanted weakAscent_weaklyIncreasing_card (n : ℕ) :
    {w : List ℕ | w.length = n ∧ IsWeakAscentSeq w ∧ w.Pairwise (· ≤ ·)}.ncard = catalan n ∧
      {w : List ℕ | w.length = n ∧ IsWeakAscentSeq w ∧ w.Pairwise (· ≤ ·) ∧
          ¬ ContainsPattern w [0, 0, 0]}.ncard = motzkinNumber n

/-- **Weak ascent Wilf equivalence, class 99.** Write $\mathrm{WA}_n(P)$ for the set of weak
ascent sequences of length $n$ avoiding every pattern in $P$, with patterns written as words (for
example $011$). The pattern sets $\{011, 100, 102, 201\}$ and $\{011, 100, 120, 201\}$ are WA-Wilf
equivalent: for every $n \ge 0$,
$|\mathrm{WA}_n(\{011, 100, 102, 201\})| = |\mathrm{WA}_n(\{011, 100, 120, 201\})|$.

Source: the extracted record drops the `w` marker on `∼`; the weak-ascent reading follows from the
class number (the paper has 74 A-classes, and its class table numbered past 74 is the WA table).

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 5 (`integers-2025-A80-thm-5`). -/
public theorem_wanted weakAscent_wilf_class99 (n : ℕ) :
    (weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [1, 0, 2], [2, 0, 1]} n).ncard =
      (weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [1, 2, 0], [2, 0, 1]} n).ncard

/-- **Weak ascent Wilf equivalence and generating function, class 93.** Write $\mathrm{WA}_n(P)$
for the set of weak ascent sequences of length $n$ avoiding every pattern in $P$, with patterns
written as words (for example $011$). The pattern sets $P = \{011, 102, 120, 201\}$ and
$\{011, 102, 120, 210\}$ are WA-Wilf equivalent, that is,
$|\mathrm{WA}_n(P)| = |\mathrm{WA}_n(\{011, 102, 120, 210\})|$ for every $n \ge 0$. Moreover, the
formal power series $F(x) = \sum_{n \ge 1} |\mathrm{WA}_n(P)| \, x^n$ in $\mathbb{Z}[[x]]$
(without the $n = 0$ term) satisfies $F(x) \, (1 - 2x)(1 - x)^2 = x(2x^2 - 2x + 1)$, that is,
$F(x) = \frac{x(2x^2 - 2x + 1)}{(1 - 2x)(1 - x)^2}$.

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

/-- **Weak-ascent Wilf equivalence in Class 162.** For every natural number $n$, the number of
weak ascent sequences of length $n$ avoiding every pattern in $\{010, 100, 101, 120\}$ equals the
number avoiding every pattern in $\{010, 100, 110, 120\}$.

That is, the two sets are WA-Wilf equivalent.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 8 (`integers-2025-A80-thm-8`). -/
public theorem_wanted weakAscent_wilf_class162 (n : ℕ) :
    (weakAscentAvoiders {[0, 1, 0], [1, 0, 0], [1, 0, 1], [1, 2, 0]} n).ncard =
      (weakAscentAvoiders {[0, 1, 0], [1, 0, 0], [1, 1, 0], [1, 2, 0]} n).ncard

/-- **Weak-ascent Wilf equivalence in Class 205.** For every natural number $n$, the number of
weak ascent sequences of length $n$ avoiding every pattern in $\{100, 102, 120, 201\}$ equals the
number avoiding every pattern in $\{102, 110, 120, 201\}$.

That is, the two sets are WA-Wilf equivalent.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 9 (`integers-2025-A80-thm-9`). -/
public theorem_wanted weakAscent_wilf_class205 (n : ℕ) :
    (weakAscentAvoiders {[1, 0, 0], [1, 0, 2], [1, 2, 0], [2, 0, 1]} n).ncard =
      (weakAscentAvoiders {[1, 0, 2], [1, 1, 0], [1, 2, 0], [2, 0, 1]} n).ncard

/-- **Weak-ascent Wilf equivalence in Class 206.** For every natural number $n$, the number of
weak ascent sequences of length $n$ avoiding every pattern in $\{100, 102, 120, 210\}$ equals
the number avoiding every pattern in $\{101, 102, 120, 201\}$, the number avoiding every
pattern in $\{101, 102, 120, 210\}$ and the number avoiding every pattern in
$\{102, 110, 120, 210\}$.

That is, the four sets are WA-Wilf equivalent.

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

/-- **Weak-ascent Wilf equivalence in Class 219.** For every natural number $n$, the number of
weak ascent sequences of length $n$ avoiding every pattern in $\{100, 101, 102, 201\}$ equals
the number avoiding every pattern in $\{100, 110, 120, 201\}$.

That is, the two sets are WA-Wilf equivalent. They are not Wilf equivalent for ascent
sequences: the numbers of ascent sequences avoiding them first differ at length $5$, where
they are $29$ and $30$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 11 (`integers-2025-A80-thm-11`). -/
public theorem_wanted weakAscent_wilf_class219 (n : ℕ) :
    (weakAscentAvoiders {[1, 0, 0], [1, 0, 1], [1, 0, 2], [2, 0, 1]} n).ncard =
      (weakAscentAvoiders {[1, 0, 0], [1, 1, 0], [1, 2, 0], [2, 0, 1]} n).ncard

/-- **Fibonacci closed form of a binomial sum with powers of two.** Let $F_m$ denote the
Fibonacci numbers, with $F_0 = 0$ and $F_1 = 1$. For every natural number $n \ge 4$,
$$\sum_{k=1}^{\lfloor n/3 \rfloor - 1} \left( \binom{n-k-4}{2k} 2^{n-3k-4} +
\binom{n-k-4}{2k-1} 2^{n-3k-3} \right) + 2^{n-4} = F_{2n-7}.$$
The sum is empty for $n < 6$. When $3$ divides $n$, the last index $k = n/3 - 1$ gives the
exponent $n - 3k - 4 = -1$, but there $\binom{n-k-4}{2k} = 0$, and the product
$\binom{n-k-4}{2k} 2^{n-3k-4}$ is read as $0$; the other product in that summand is $1$.

The source states this as the sum being $F_{2n-7} - 2^{n-4}$. The summand is reconstructed from
an extracted display of the source's Proposition 2(i), as the full text was not available; exact
computation confirms the identity for $4 \le n \le 500$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Proposition 3 (`integers-2025-A80-prop-3`), with the sum of Proposition 2(i). -/
public theorem_wanted sum_choose_mul_two_pow_add_two_pow_eq_fib (n : ℕ) (hn : 4 ≤ n) :
    (∑ k ∈ Finset.Icc 1 (n / 3 - 1),
        (Nat.choose (n - k - 4) (2 * k) * 2 ^ (n - 3 * k - 4) +
          Nat.choose (n - k - 4) (2 * k - 1) * 2 ^ (n - 3 * k - 3))) + 2 ^ (n - 4) =
      Nat.fib (2 * n - 7)

/-- **Reducible pattern sets (Theorem 3).** For a set $P$ of patterns, let $A_n(P)$ and
$WA_n(P)$ be the sets of ascent sequences and of weak ascent sequences of length $n$ that
avoid every pattern in $P$. For each set $C$ of patterns and each pattern $\tau$ listed below,
with $B = C \cup \{\tau\}$, we have $A_n(B) = A_n(C)$ and $WA_n(B) = WA_n(C)$ for every
natural number $n$:

- $C = \{001\}$ and $\tau \in \{101, 102, 201\}$;
- $C = \{011\}$ and $\tau \in \{101, 110\}$;
- $C = \{012\}$ and $\tau \in \{102, 120\}$;
- $C = \{021\}$ and $\tau \in \{201, 210\}$;
- $C = \{000, 001\}$ and $\tau = 100$;
- $C = \{000, 011\}$ and $\tau \in \{100, 201, 210\}$;
- $C = \{000, 012\}$ and $\tau \in \{201, 210\}$;
- $C = \{000, 021\}$ and $\tau = 100$;
- $C = \{001, 010\}$ and $\tau \in \{021, 100, 110, 120, 210\}$;
- $C = \{001, 011\}$ and $\tau = 021$;
- $C = \{001, 012\}$ and $\tau = 021$;
- $C = \{001, 110\}$ and $\tau = 210$;
- $C = \{001, 120\}$ and $\tau = 210$;
- $C = \{010, 011\}$ and $\tau = 100$;
- $C = \{010, 012\}$ and $\tau \in \{101, 201\}$;
- $C = \{010, 021\}$ and $\tau \in \{100, 101, 102, 110, 120\}$;
- $C = \{001, 011, 012\}$, $\{001, 011, 100\}$ or $\{001, 012, 100\}$, and $\tau = 210$.

These are $36$ pairs $C \subsetneq B$. The paper writes $C \sim_r B$ and takes the result from
its reference [5].

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

/-- **Motzkin counts for weak ascent sequences in Class 86.** Let $M_n$ denote the Motzkin
numbers. For every natural number $n \ge 3$, the number of weak ascent sequences of length $n$
avoiding every pattern in $\{000, 021, 101, 120\}$, the number avoiding every pattern in
$\{000, 021, 101, 102\}$ and the number avoiding every pattern in $\{000, 021, 110, 120\}$ are
each equal to $M_n + M_{n-2}$.

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

/-- **Weak-ascent Wilf equivalence in Class 61.** For every natural number $n$, the number of
weak ascent sequences of length $n$ avoiding every pattern in $\{010, 011, 102, 201\}$ equals the
number avoiding every pattern in $\{010, 011, 120, 201\}$.

That is, the two sets are WA-Wilf equivalent.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 6 (`integers-2025-A80-thm-6`). -/
public theorem_wanted weakAscent_wilf_class61 (n : ℕ) :
    (weakAscentAvoiders {[0, 1, 0], [0, 1, 1], [1, 0, 2], [2, 0, 1]} n).ncard =
      (weakAscentAvoiders {[0, 1, 0], [0, 1, 1], [1, 2, 0], [2, 0, 1]} n).ncard

/-- **Generating function for weak ascent sequences avoiding 101, 102, 110 and 201.** Let $a_n$
be the number of weak ascent sequences of length $n$ that avoid each of the patterns $101$,
$102$, $110$ and $201$, and let $F = \sum_{n \ge 0} a_n X^n$ in $\mathbb{Q}[[X]]$. For every
power series $S \in \mathbb{Q}[[X]]$ with $S^2 = 1 - 4X$ and constant term $1$,
$$F \cdot 2(1 - X)(1 - 4X - X^2) = (2 - 3X - X^2) S - X - X^2.$$

Such an $S$ is the power series $\sqrt{1 - 4X}$, and $1 - X$ and $1 - 4X - X^2$ are invertible,
so this is the formula
$F = \frac{(2 - 3X - X^2)\sqrt{1 - 4X} - X - X^2}{2(1 - X)(1 - 4X - X^2)}$ with the denominator
cleared.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 12 (`integers-2025-A80-thm-12`). -/
public theorem_wanted weakAscent_class211_generatingFunction (S : PowerSeries ℚ)
    (hS : S ^ 2 = 1 - 4 * PowerSeries.X) (hS0 : PowerSeries.constantCoeff S = 1) :
    PowerSeries.mk (fun n : ℕ =>
        ((weakAscentAvoiders {[1, 0, 1], [1, 0, 2], [1, 1, 0], [2, 0, 1]} n).ncard : ℚ)) *
        (2 * (1 - PowerSeries.X) * (1 - 4 * PowerSeries.X - PowerSeries.X ^ 2)) =
      (2 - 3 * PowerSeries.X - PowerSeries.X ^ 2) * S - PowerSeries.X - PowerSeries.X ^ 2

/-- **Big entry.** Let $w = w_1 \cdots w_n$ be a word over $\mathbb{N}$ and $2 \le k \le n$. The
entry $w_k$ is a big entry of $w$ if it equals $1$ plus the number of weak ascents of
$w_1 \cdots w_{k-1}$, that is, of positions $j < k - 1$ with $w_j \le w_{j+1}$. In a weak ascent
sequence this is the largest value allowed at position $k$. The entry $w_k$ is referred to by its
zero-based index $i = k - 1$, so the index ranges over $1 \le i < n$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3
(definition of big entry). -/
public def IsBigEntry (w : List ℕ) (i : ℕ) : Prop :=
  1 ≤ i ∧ i < w.length ∧ w.getD i 0 = wordWeakAscents (w.take i) + 1

public instance (w : List ℕ) (i : ℕ) : Decidable (IsBigEntry w i) := by
  unfold IsBigEntry; infer_instance

/-- **Big entries of $00203413$.** In the word $w = 00203413$, with positions numbered from $1$,
the entries $w_3 = 2$ and $w_6 = 4$ are big entries and the entry $w_7 = 1$ is not.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3. -/
public theorem isBigEntry_example :
    IsBigEntry [0, 0, 2, 0, 3, 4, 1, 3] 2 ∧ IsBigEntry [0, 0, 2, 0, 3, 4, 1, 3] 5 ∧
      ¬ IsBigEntry [0, 0, 2, 0, 3, 4, 1, 3] 6 := by
  decide

/-- **Position of the last descent top.** For a finite sequence $w = w_1 w_2 \cdots w_m$ of
natural numbers, a descent of $w$ is an index $1 \le i < m$ with $w_i > w_{i+1}$, and $w_i$ is
its descent top. The position of the last descent top of $w$ is the largest index $i$ with
$w_i > w_{i+1}$ (positions counted from $1$), and it is $0$ if $w$ has no descent.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3
(definition of `W_{n,k}`). -/
public def lastDescentTop (w : List ℕ) : ℕ :=
  ((Finset.range (w.length - 1)).filter fun i => w.getD (i + 1) 0 < w.getD i 0).sup (· + 1)

/-- **Examples of the last descent top.** Each of the sequences $0010$, $0020$, $0021$ and
$0120$ has its last descent top at position $3$, and the sequence $012$, which has no
descent, has last descent top position $0$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3. -/
public theorem lastDescentTop_example :
    lastDescentTop [0, 0, 1, 0] = 3 ∧ lastDescentTop [0, 0, 2, 0] = 3 ∧
      lastDescentTop [0, 0, 2, 1] = 3 ∧ lastDescentTop [0, 1, 2, 0] = 3 ∧
      lastDescentTop [0, 1, 2] = 0 := by
  decide

/-- **The sets $U_{n,j}$.** Let $W_n = WA_n(011, 100, 201, 210)$ be the set of weak ascent
sequences of length $n$ that avoid each of the patterns $011$, $100$, $201$ and $210$. For
natural numbers $n$ and $j$, $U_{n,j}$ is the set of sequences $w = w_1 w_2 \cdots w_n$ in
$W_n$ such that the last descent top of $w$ is at position $n - 1$, $w$ has a big entry, the
first $n - 2$ entries of $w$ are not all $0$, $w_{n-1} \ne n - 2$, and $w_{n-1} = w_n + j$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3.2
(definition of `U_{n,j}`). -/
public def quadrupleUSet (n j : ℕ) : Set (List ℕ) :=
  {w | w ∈ weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} n ∧
    lastDescentTop w = n - 1 ∧ (∃ i < n, IsBigEntry w i) ∧ (∃ i < n - 2, w.getD i 0 ≠ 0) ∧
    w.getD (n - 2) 0 ≠ n - 2 ∧ w.getD (n - 2) 0 = w.getD (n - 1) 0 + j}

/-- **$U_{0,j}$ is empty.** For every natural number $j$, the set $U_{0,j}$ is empty.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3.2. -/
public theorem quadrupleUSet_zero (j : ℕ) : quadrupleUSet 0 j = ∅ := by
  ext w
  simp [quadrupleUSet]

/-- **The sets $V_{n,j}$.** Let $W_n = WA_n(011, 100, 201, 210)$ be the set of weak ascent
sequences of length $n$ that avoid each of the patterns $011$, $100$, $201$ and $210$. For
natural numbers $n$ and $j$, $V_{n,j}$ is the set of sequences $w = w_1 w_2 \cdots w_n$ in
$W_n$ such that the last descent top of $w$ is at position $n - 2$, $w_n \le n - 3$,
$w_{n-1} \ne 0$, and $w_{n-2} = w_{n-1} + j$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3.2
(definition of `V_{n,j}`). -/
public def quadrupleVSet (n j : ℕ) : Set (List ℕ) :=
  {w | w ∈ weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} n ∧
    lastDescentTop w = n - 2 ∧ w.getD (n - 1) 0 ≤ n - 3 ∧ w.getD (n - 2) 0 ≠ 0 ∧
    w.getD (n - 3) 0 = w.getD (n - 2) 0 + j}

/-- **$V_{n,j}$ lies in $W_n$.** For all natural numbers $n$ and $j$, the set $V_{n,j}$ is
contained in $W_n = WA_n(011, 100, 201, 210)$, the set of weak ascent sequences of length $n$
that avoid each of the patterns $011$, $100$, $201$ and $210$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3.2. -/
public theorem quadrupleVSet_subset (n j : ℕ) :
    quadrupleVSet n j ⊆ weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} n :=
  fun _ h => h.1

/-- **Successors of big entries in $W_n$.** Let $W_n$ be the set of weak ascent sequences of length
$n$ avoiding the patterns $011$, $100$, $201$ and $210$, and let $w = w_1 \cdots w_n \in W_n$. If
$2 \le k \le n - 1$ and $w_k$ is a big entry of $w$, then either $w_{k+1}$ is a big entry, or
$w_{k+1} < w_k$ and $w_j$ is a big entry for every $j$ with $k + 2 \le j \le n$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Lemma 1 (`integers-2025-A80-lem-1`). -/
public theorem_wanted isBigEntry_succ_or_descent (n : ℕ) (w : List ℕ)
    (hw : w ∈ weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} n) (k : ℕ)
    (hk : 2 ≤ k) (hkn : k ≤ n - 1) (hbig : IsBigEntry w (k - 1)) :
    IsBigEntry w k ∨
      (w.getD k 0 < w.getD (k - 1) 0 ∧ ∀ j, k + 2 ≤ j → j ≤ n → IsBigEntry w (j - 1))

/-- **Recurrence for $|U_{n,1}|$ and $|V_{n,1}|$ (Lemma 2).** Let $f$ be either of the
sequences $u_n = |U_{n,1}|$ and $v_n = |V_{n,1}|$. Then $f_j = 0$ for every $j \le 5$,
$f_6 = 1$, and $f_n = 5 f_{n-1} - 7 f_{n-2} + 2 f_{n-3}$ for every $n \ge 7$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Lemma 2 (`integers-2025-A80-lem-2`). -/
public theorem_wanted quadrupleUSet_quadrupleVSet_recurrence :
    ∀ f ∈ [fun n => (quadrupleUSet n 1).ncard, fun n => (quadrupleVSet n 1).ncard],
      (∀ j ≤ 5, f j = 0) ∧ f 6 = 1 ∧
        ∀ n, 7 ≤ n → (f n : ℤ) = 5 * f (n - 1) - 7 * f (n - 2) + 2 * f (n - 3)

/-- **Sum formulas for $|U_{n,1}|$ and $|V_{n,1}|$ (Proposition 2).** For every natural number
$n$ let $f(n, a) = \min(n - 3 - a, \lfloor (a - 1)/2 \rfloor)$ and
$$
S(n) = \sum_{a=2}^{n-4} \sum_{k=1}^{f(n,a)} \left( \binom{a-2}{2k} 2^{a-2k-2} +
\binom{a-2}{2k-1} 2^{a-2k-1} \right) (n - k - a - 2).
$$
Then for every $n \ge 1$
$$
|U_{n,1}| = \sum_{k=1}^{\lfloor n/3 \rfloor - 1} \left( \binom{n-k-4}{2k} 2^{n-3k-4} +
\binom{n-k-4}{2k-1} 2^{n-3k-3} \right)
$$
and
$$
|V_{n,1}| = \sum_{a=2}^{n-4} 2^{a-2} (n - a - 3) + S(n),
$$
and for every $n \ge 4$
$$
|V_{n,1}| = 2^{n-4} - n + 3 + S(n).
$$

A sum whose upper limit is below its lower limit is empty, and an exponent such as
$n - 3k - 4$ is negative only where the binomial coefficient multiplying it is $0$; such a
term is $0$. The last formula is stated only for $n \ge 4$: at $n = 3$ the expression
$2^{n-4} - n + 3$ equals $1/2$, while $\sum_{a=2}^{n-4} 2^{a-2} (n - a - 3)$ is $0$.

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
