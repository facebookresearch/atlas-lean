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
public import MathlibExt.Combinatorics.Enumerative.AscentSequenceBinomialFibonacci
public import MathlibExt.Combinatorics.Enumerative.AscentSequenceQuadrupleCardFormulas
public import MathlibExt.Combinatorics.Enumerative.AscentSequenceQuadruplePatterns
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
public import MathlibExt.Combinatorics.Enumerative.WeakAscentWilfClass162
public import MathlibExt.Combinatorics.Enumerative.WeakAscentWilfClass205

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
