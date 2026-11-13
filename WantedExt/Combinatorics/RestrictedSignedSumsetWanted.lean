/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import MathlibExt.Combinatorics.AP.Basic
public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset

/-!
# Restricted signed sumsets (statements)

Statement-only targets from Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse
Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81.
`restrictedSignedSumset h A` is `h^∧_± A`, the sums `Σ λ_i a_i` with `λ_i ∈ {-1, 0, 1}` and
`Σ |λ_i| = h`; `restrictedSumset h A` is `h^∧ A`. Ordered sets `a_1 < ⋯ < a_k` are strictly
increasing maps `Fin k → ℤ`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Set of values of a finite integer sequence.** For a sequence $a_0, \dots, a_{k-1}$ of
integers, this is the finite set $\{a_i : 0 \le i < k\}$ of its values.

No order or injectivity is assumed; the statements that use it assume what they need.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, notation for ordered finite sets. -/
public def orderedFinset {k : ℕ} (a : Fin k → ℤ) : Finset ℤ :=
  Finset.univ.image a

/-- **Initial segment of a finite integer sequence.** For a sequence $a_0, \dots, a_{k-1}$ of
integers and a natural number $n$, the initial segment of length $n$ is the set
$\{a_i : 0 \le i < k,\ i < n\}$ of the values at indices below $n$; it is the set of all values
of the sequence when $n \ge k$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, notation for initial subsets. -/
public def initialSegment {k : ℕ} (a : Fin k → ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.univ.filter fun i : Fin k => (i : ℕ) < n).image a

/-- **Finite integer sequences in arithmetic progression.** A sequence $a_0, \dots, a_{k-1}$ of
integers is an arithmetic progression with common difference $d$ if $d > 0$ and
$a_{i+1} = a_i + d$ for every $i$ with $i + 1 < k$.

The condition is stated on adjacent terms, so no nonemptiness assumption is needed to name a
first term.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, definition of arithmetic progression. -/
public def IsIndexedAP {k : ℕ} (a : Fin k → ℤ) (d : ℤ) : Prop :=
  0 < d ∧ ∀ (i j : Fin k), (i : ℕ) + 1 = (j : ℕ) → a j = a i + d

/-- **Dilation of a finite set of integers.** For an integer $d$ and a finite set $B$ of
integers, the dilation $d \cdot B$ is the set $\{db : b \in B\}$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, dilation notation. -/
public def scaleFinset (d : ℤ) (B : Finset ℤ) : Finset ℤ :=
  B.image (fun b => d * b)

/-- **The first $k$ odd positive integers.** For a natural number $k$, this is the set of integers
$\{1, 3, \dots, 2k - 1\} = \{2i + 1 : 0 \le i < k\}$; it is empty when $k = 0$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, odd-progression notation. -/
public def oddProgression (k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun i : ℕ => 2 * (i : ℤ) + 1)

/-- **Values of a finite integer sequence after its first term.** For a sequence
$a_0, \dots, a_{k-1}$ of integers, this is the set $\{a_i : 1 \le i < k\}$. When the sequence is
strictly increasing, it is the set $A' = A \setminus \{a_0\}$ obtained from
$A = \{a_0, \dots, a_{k-1}\}$ by removing its least element.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, notation `A'`. -/
public def tailFinset {k : ℕ} (a : Fin k → ℤ) : Finset ℤ :=
  (Finset.univ.filter fun i : Fin k => 0 < (i : ℕ)).image a

/-- **Zero-based integer interval.** For a natural number $k$, the integer interval $[0, k-1]$ is
the set $\{0, 1, \dots, k-1\}$ of integers $i$ with $0 \le i < k$; it is empty when $k = 0$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, interval notation. -/
public def zeroInterval (k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun i : ℕ => (i : ℤ))

/-- **The restricted signed 4-fold sumset of $\{1, 3, 5, 7, 9\}$.** The restricted signed 4-fold
sumset $4^{\wedge}_{\pm} \{1, 3, 5, 7, 9\}$ has exactly $25$ elements.

This is an extremal five-element set of positive integers in Theorem 10 of the source: it
attains that theorem's lower bound $25$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 10 example. -/
public theorem card_restrictedSignedSumset_four_odd_five :
    (restrictedSignedSumset 4 {1, 3, 5, 7, 9}).card = 25 := by
  decide +kernel

/-- **The restricted signed 4-fold sumset of $\{0, 1, 2, 4, 6\}$.** The restricted signed 4-fold
sumset $4^{\wedge}_{\pm} \{0, 1, 2, 4, 6\}$ has exactly $21 = 8 \cdot 5 - 19$ elements.

This is the extremal value $8k - 19$ at $k = 5$ of the lower bound in Theorem 11 of the source.
Since $\{0, 1, 2, 4, 6\}$ differs from $d \cdot \{0, 1, 2, 3, 4\}$ for every integer $d$, it
refutes the inverse sentence of that theorem (the counterexample is ours, not the paper's).

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 11 (lower bound `8k - 19` at `k = 5`). -/
public theorem card_restrictedSignedSumset_four_counterexample :
    (restrictedSignedSumset 4 {0, 1, 2, 4, 6}).card = 21 := by
  decide +kernel

/-- **$\{0, 1, 2, 4, 6\}$ is not a dilate of $\{0, 1, 2, 3, 4\}$.** For every integer $d$, the
set $\{0, 1, 2, 4, 6\}$ differs from the dilation
$d \cdot \{0, 1, 2, 3, 4\} = \{0, d, 2d, 3d, 4d\}$.

Indeed, $1 = di$ with $0 \le i \le 4$ forces $d = \pm 1$, and then $6$ is not of the form $di$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 11 (inverse sentence, `A = d * [0,k-1]`). -/
public theorem ne_scaleFinset_zeroInterval_five (d : ℤ) :
    ({0, 1, 2, 4, 6} : Finset ℤ) ≠ scaleFinset d (zeroInterval 5) := by
  intro h
  have h1 : (1 : ℤ) ∈ scaleFinset d (zeroInterval 5) := h ▸ by decide
  have h6 : (6 : ℤ) ∈ scaleFinset d (zeroInterval 5) := h ▸ by decide
  simp only [scaleFinset, zeroInterval, Finset.mem_image, Finset.mem_range] at h1 h6
  obtain ⟨_, ⟨i, hi, rfl⟩, hdi⟩ := h1
  obtain ⟨_, ⟨j, hj, rfl⟩, hdj⟩ := h6
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdi with rfl | rfl <;> omega

/-- **The restricted signed 3-fold sumset of $\{1, 2, 3, 4\}$.** The restricted signed 3-fold
sumset $3^{\wedge}_{\pm} \{1, 2, 3, 4\}$ has exactly $19$ elements.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Definition of restricted signed sumset. -/
public theorem card_restrictedSignedSumset_three_four :
    (restrictedSignedSumset 3 {1, 2, 3, 4}).card = 19 := by
  decide

/-- **Lower bounds for restricted signed sumsets of nonnegative integers.** Let $h$ and $k$ be
integers with $1 \le h \le k$, let $A$ be a set of $k$ nonnegative integers, and write
$h^{\wedge}_{\pm} A$ for the restricted signed $h$-fold sumset of $A$. If $0 \notin A$, then
$2|h^{\wedge}_{\pm} A| \ge 4(hk - h^2) + h(h+1) + 2$; if $0 \in A$, then
$2|h^{\wedge}_{\pm} A| \ge 4(hk - h^2) + h(h-1) + 2$.

The source states these bounds divided by $2$. Its remark that they are optimal for
$h = 1$, $h = 2$ and $h = k$ is not formalized.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 1. -/
public theorem_wanted card_restrictedSignedSumset_general_lower_bounds
    (h k : ℕ) (A : Finset ℤ) (hh : 0 < h) (hk : h ≤ k) (hcard : A.card = k)
    (hnonneg : ∀ a ∈ A, 0 ≤ a) :
    (0 ∉ A →
      2 * ((restrictedSignedSumset h A).card : ℤ) ≥
        4 * ((h : ℤ) * k - (h : ℤ) ^ 2) + (h : ℤ) * (h + 1) + 2) ∧
    (0 ∈ A →
      2 * ((restrictedSignedSumset h A).card : ℤ) ≥
        4 * ((h : ℤ) * k - (h : ℤ) ^ 2) + (h : ℤ) * (h - 1) + 2)

/-- **Nathanson's bound for restricted sumsets and its inverse.** Let $A$ be a nonempty finite
set of $k$ integers and let $h$ be a natural number with $1 \le h \le k$. Then the restricted
sumset $h^{\wedge} A$ has at least $hk - h^2 + 1$ elements. Moreover, if $k \ge 5$ and
$2 \le h \le k - 2$, then $h^{\wedge} A$ has exactly $hk - h^2 + 1$ elements if and only if there
are integers $a$ and $d > 0$ such that $A$ is the arithmetic progression of length $k$ with
first term $a$ and difference $d$, that is, $A = \{a + nd : 0 \le n < k\}$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 2. -/
public theorem_wanted card_restrictedSumset_ge_and_eq_iff_ap
    (h : ℕ) (A : Finset ℤ) (hA : A.Nonempty) (hh : 1 ≤ h) (hhA : h ≤ A.card) :
    ((restrictedSumset h A).card : ℤ) ≥ (h : ℤ) * A.card - (h : ℤ) ^ 2 + 1 ∧
    (5 ≤ A.card → 2 ≤ h → h ≤ A.card - 2 →
      (((restrictedSumset h A).card : ℤ) = (h : ℤ) * A.card - (h : ℤ) ^ 2 + 1 ↔
        ∃ a d : ℤ, 0 < d ∧ (A : Set ℤ).IsAPOfLengthWith A.card a d))

/-- **Restricted signed sumsets of arithmetic progressions with one more term than summands.**
Let $h \ge 3$ be a natural number and let $a_1 < a_2 < \cdots < a_{h+1}$ be positive integers that
form an arithmetic progression with common difference $d > 0$, that is, $a_{i+1} = a_i + d$ for
$1 \le i \le h$. Let $A = \{a_1, \ldots, a_{h+1}\}$ and let $h^{\wedge}_{\pm} A$ be the
restricted signed sumset of $A$. Then $|h^{\wedge}_{\pm} A| \ge (h+1)^2$ if $d = 2a_1$, and
$|h^{\wedge}_{\pm} A| \ge (h+1)^2 + 1$ otherwise. Moreover, $|h^{\wedge}_{\pm} A| = (h+1)^2$ if
and only if $d = 2a_1$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 3. -/
public theorem_wanted card_restrictedSignedSumset_ap_h_add_one
    (h : ℕ) (hh : 3 ≤ h) (a : Fin (h + 1) → ℤ) (d : ℤ)
    (ha : StrictMono a) (hpos : ∀ i, 0 < a i) (hap : IsIndexedAP a d) :
    (((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≥
      if d = 2 * a ⟨0, by omega⟩ then ((h + 1 : ℕ) : ℤ) ^ 2
      else ((h + 1 : ℕ) : ℤ) ^ 2 + 1) ∧
    (((restrictedSignedSumset h (orderedFinset a)).card : ℤ) =
        ((h + 1 : ℕ) : ℤ) ^ 2 ↔ d = 2 * a ⟨0, by omega⟩)

/-- **Lower bound for restricted signed sumsets of arithmetic progressions.** Let $h \ge 3$ and
$k \ge h + 1$ be natural numbers, and let $a_1 < a_2 < \cdots < a_k$ be integers with $a_1 > 0$
that form an arithmetic progression with common difference $d > 0$, that is,
$a_{i+1} = a_i + d$ for $1 \le i < k$. Let $A = \{a_1, \ldots, a_k\}$ and let $h^{\wedge}_{\pm} A$
be the restricted signed sumset of $A$. Then $|h^{\wedge}_{\pm} A| \ge 2hk - h^2 + 1$ if
$d = 2a_1$, and $|h^{\wedge}_{\pm} A| \ge 2hk - h^2 + 2$ otherwise. Moreover,
$|h^{\wedge}_{\pm} A| = 2hk - h^2 + 1$ if and only if $d = 2a_1$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Corollary 1. -/
public theorem_wanted card_restrictedSignedSumset_ap_ge
    (h k : ℕ) (hh : 3 ≤ h) (hk : h + 1 ≤ k) (a : Fin k → ℤ) (d : ℤ)
    (ha : StrictMono a) (hpos : 0 < a ⟨0, by omega⟩) (hap : IsIndexedAP a d) :
    (((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≥
      if d = 2 * a ⟨0, by omega⟩ then 2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 1
      else 2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 2) ∧
    (((restrictedSignedSumset h (orderedFinset a)).card : ℤ) =
        2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 1 ↔ d = 2 * a ⟨0, by omega⟩)

/-- **Restricted signed sumsets of arithmetic progressions containing zero.** Let $h$ and $k$ be
natural numbers with $4 \le h \le k - 1$, and let $0 = a_1 < a_2 < \cdots < a_k$ be nonnegative
integers that form an arithmetic progression with common difference $d > 0$, that is,
$a_{i+1} = a_i + d$ for $1 \le i < k$. Let $A = \{a_1, \ldots, a_k\}$ and let $h^{\wedge}_{\pm} A$
be the restricted signed sumset of $A$. Then $|h^{\wedge}_{\pm} A| = 2hk - h(h+1) + 1$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 4. -/
public theorem_wanted card_restrictedSignedSumset_ap_zero
    (h k : ℕ) (hh : 4 ≤ h) (hk : h ≤ k - 1) (a : Fin k → ℤ) (d : ℤ)
    (ha : StrictMono a) (hnonneg : ∀ i, 0 ≤ a i)
    (hzero : a ⟨0, by omega⟩ = 0) (hap : IsIndexedAP a d) :
    ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) =
      2 * (h : ℤ) * k - (h : ℤ) * (h + 1) + 1

/-- **Inverse theorem for the extremal restricted signed sumset of positive integers.** Let $h$
and $k$ be natural numbers with $4 \le h \le k - 1$, and let
$A = \{a_1 < a_2 < \cdots < a_k\}$ be a set of $k$ positive integers. Write
$A_{h+1} = \{a_1, \dots, a_{h+1}\}$, $A' = \{a_2, \dots, a_k\}$ and $-A' = \{-x : x \in A'\}$.
Suppose that the restricted signed sumset $h^{\wedge}_{\pm} A$ has exactly $2hk - h^2 + 1$
elements and that at least one of the following holds:
(a) there is $d > 0$ with $a_{i+1} = a_i + d$ for all $1 \le i < k$;
(b) $A_{h+1} = \{b + nd : 0 \le n \le h\}$ for some integers $b$ and $d > 0$;
(c) $h^{\wedge}_{\pm} A_{h+1}$ has at least $(h+1)^2$ elements and $4 \le h \le k - 3$;
(d) $h^{\wedge}_{\pm} A = h^{\wedge}(-A') \cup h^{\wedge}_{\pm} A_{h+1} \cup h^{\wedge} A'$, where
$h^{\wedge}$ is the restricted sumset, and $A' = \{b + nd : 0 \le n < k - 1\}$ for some
integers $b$ and $d > 0$;
(e) $h^{\wedge}_{\pm} A_{h+1}$ has at least $(h+1)^2$ elements and
$A' = \{b + nd : 0 \le n < k - 1\}$ for some integers $b$ and $d > 0$.
Then $A = a_1 \cdot \{1, 3, \dots, 2k - 1\} = \{(2i - 1) a_1 : 1 \le i \le k\}$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 5. -/
public theorem_wanted eq_scaled_oddProgression_of_extremal
    (h k : ℕ) (hh : 4 ≤ h) (hk : h ≤ k - 1) (a : Fin k → ℤ)
    (ha : StrictMono a) (hpos : ∀ i, 0 < a i)
    (heq : ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) =
      2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 1)
    (hcase :
      (∃ d, IsIndexedAP a d) ∨
      (∃ b d, 0 < d ∧ (initialSegment a (h + 1) : Set ℤ).IsAPOfLengthWith (h + 1) b d) ∨
      (((restrictedSignedSumset h (initialSegment a (h + 1))).card : ℤ) ≥
          ((h + 1 : ℕ) : ℤ) ^ 2 ∧ 4 ≤ h ∧ h ≤ k - 3) ∨
      (restrictedSignedSumset h (orderedFinset a) =
          restrictedSumset h ((tailFinset a).image (-·)) ∪
            restrictedSignedSumset h (initialSegment a (h + 1)) ∪
            restrictedSumset h (tailFinset a) ∧
        ∃ b d, 0 < d ∧ (tailFinset a : Set ℤ).IsAPOfLengthWith (k - 1) b d) ∨
      (((restrictedSignedSumset h (initialSegment a (h + 1))).card : ℤ) ≥
          ((h + 1 : ℕ) : ℤ) ^ 2 ∧
        ∃ b d, 0 < d ∧ (tailFinset a : Set ℤ).IsAPOfLengthWith (k - 1) b d)) :
    orderedFinset a = scaleFinset (a ⟨0, by omega⟩) (oddProgression k)

/-- **Inverse theorem for the extremal restricted signed sumset of sets containing zero.** Let
$h$ and $k$ be natural numbers with $4 \le h \le k - 1$, and let
$A = \{a_0 < a_1 < \cdots < a_{k-1}\}$ be a set of $k$ nonnegative integers with $a_0 = 0$.
Write $A_h = \{a_0, \dots, a_h\}$, $A' = \{a_1, \dots, a_{k-1}\}$ and
$-A' = \{-x : x \in A'\}$. Suppose that the restricted signed sumset $h^{\wedge}_{\pm} A$ has
exactly $2hk - h(h+1) + 1$ elements and that at least one of the following holds:
(a) there is $d > 0$ with $a_{i+1} = a_i + d$ for all $0 \le i < k - 1$;
(b) $A_h = \{b + nd : 0 \le n \le h\}$ for some integers $b$ and $d > 0$;
(c) $h^{\wedge}_{\pm} A_h$ has at least $h(h+1) + 1$ elements and $4 \le h \le k - 3$;
(d) $h^{\wedge}_{\pm} A = h^{\wedge}(-A') \cup h^{\wedge}_{\pm} A_h \cup h^{\wedge} A'$, where
$h^{\wedge}$ is the restricted sumset, and $A' = \{b + nd : 0 \le n < k - 1\}$ for some
integers $b$ and $d > 0$;
(e) $h^{\wedge}_{\pm} A_h$ has at least $h(h+1) + 1$ elements and
$A' = \{b + nd : 0 \le n < k - 1\}$ for some integers $b$ and $d > 0$.
Then $A = a_1 \cdot \{0, 1, \dots, k - 1\} = \{i a_1 : 0 \le i < k\}$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 6. -/
public theorem_wanted eq_scaled_zeroInterval_of_extremal
    (h k : ℕ) (hh : 4 ≤ h) (hk : h ≤ k - 1) (a : Fin k → ℤ)
    (ha : StrictMono a) (hnonneg : ∀ i, 0 ≤ a i) (hzero : a ⟨0, by omega⟩ = 0)
    (heq : ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) =
      2 * (h : ℤ) * k - (h : ℤ) * (h + 1) + 1)
    (hcase :
      (∃ d, IsIndexedAP a d) ∨
      (∃ b d, 0 < d ∧ (initialSegment a (h + 1) : Set ℤ).IsAPOfLengthWith (h + 1) b d) ∨
      (((restrictedSignedSumset h (initialSegment a (h + 1))).card : ℤ) ≥
          (h : ℤ) * (h + 1) + 1 ∧ 4 ≤ h ∧ h ≤ k - 3) ∨
      (restrictedSignedSumset h (orderedFinset a) =
          restrictedSumset h ((tailFinset a).image (-·)) ∪
            restrictedSignedSumset h (initialSegment a (h + 1)) ∪
            restrictedSumset h (tailFinset a) ∧
        ∃ b d, 0 < d ∧ (tailFinset a : Set ℤ).IsAPOfLengthWith (k - 1) b d) ∨
      (((restrictedSignedSumset h (initialSegment a (h + 1))).card : ℤ) ≥
          (h : ℤ) * (h + 1) + 1 ∧
        ∃ b d, 0 < d ∧ (tailFinset a : Set ℤ).IsAPOfLengthWith (k - 1) b d)) :
    orderedFinset a = scaleFinset (a ⟨1, by omega⟩) (zeroInterval k)

/-- **Restricted signed sumsets of sets with Fibonacci-type growth.** Let $h \ge 3$ and let
$a_1 < a_2 < \dots < a_{h+1}$ be positive integers such that $a_i \ge a_{i-1} + a_{i-2}$ for
every $i$ with $4 \le i \le h + 1$. Write $h^{\wedge}_{\pm} A$ for the restricted signed
$h$-fold sumset of $A = \{a_1, \dots, a_{h+1}\}$. Then $|h^{\wedge}_{\pm} A| \ge (h+1)^2 + 1$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 7. -/
public theorem_wanted card_restrictedSignedSumset_ge_of_fibonacci_growth
    (h : ℕ) (hh : 3 ≤ h) (a : Fin (h + 1) → ℤ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i)
    (hgrowth : ∀ i : Fin (h - 2),
      a ⟨i + 3, by omega⟩ ≥ a ⟨i + 2, by omega⟩ + a ⟨i + 1, by omega⟩) :
    ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≥
      ((h + 1 : ℕ) : ℤ) ^ 2 + 1

/-- **Restricted signed sumsets under gap conditions.** Let $h \ge 3$ and let
$a_1 < a_2 < \dots < a_{h+1}$ be positive integers such that $a_3 - a_2 < 2a_1$ and
$a_2 - a_1 < 2(a_i - a_{i-1})$ for every $i$ with $4 \le i \le h + 1$. Write
$h^{\wedge}_{\pm} A$ for the restricted signed $h$-fold sumset of $A = \{a_1, \dots, a_{h+1}\}$.
Then $|h^{\wedge}_{\pm} A| \ge (h+1)^2 + 1$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 8. -/
public theorem_wanted card_restrictedSignedSumset_ge_of_gap_conditions
    (h : ℕ) (hh : 3 ≤ h) (a : Fin (h + 1) → ℤ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i)
    (hfirst : a ⟨2, by omega⟩ - a ⟨1, by omega⟩ < 2 * a ⟨0, by omega⟩)
    (hgaps : ∀ i : Fin (h - 2),
      a ⟨1, by omega⟩ - a ⟨0, by omega⟩ <
        2 * (a ⟨i + 3, by omega⟩ - a ⟨i + 2, by omega⟩)) :
    ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≥
      ((h + 1 : ℕ) : ℤ) ^ 2 + 1

/-- **Lower bound for restricted signed 4-fold sumsets of positive integers.** Let $k \ge 5$,
let $A$ be a set of $k$ positive integers, and write $4^{\wedge}_{\pm} A$ for the restricted
signed 4-fold sumset of $A$. Then $|4^{\wedge}_{\pm} A| \ge 8k - 15$. Moreover,
$|4^{\wedge}_{\pm} A| = 8k - 15$ if and only if $A = m \cdot \{1, 3, \dots, 2k - 1\}$, where
$m = \min A$ and $m \cdot B = \{mb : b \in B\}$.

The source states only that equality forces this form; the converse is included here.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 9. -/
public theorem_wanted card_restrictedSignedSumset_four_ge
    (k : ℕ) (A : Finset ℤ) (hk : 5 ≤ k) (hcard : A.card = k)
    (hpos : ∀ a ∈ A, 0 < a) :
    ((restrictedSignedSumset 4 A).card : ℤ) ≥ 8 * (k : ℤ) - 15 ∧
    (((restrictedSignedSumset 4 A).card : ℤ) = 8 * (k : ℤ) - 15 ↔
      ∃ m ∈ A, (∀ a ∈ A, m ≤ a) ∧ A = scaleFinset m (oddProgression k))

/-- **Restricted signed fourfold sumsets of five positive integers.** Let $A$ be a set of five
positive integers and let $4^{\wedge}_{\pm} A$ be the restricted signed sumset of $A$. For an
integer $m$ and a set $B$ of integers write $m \cdot B = \{mb : b \in B\}$. Then
$|4^{\wedge}_{\pm} A| \ge 25$, and $|4^{\wedge}_{\pm} A| = 25$ if and only if
$A = m \cdot \{1, 3, 5, 7, 9\}$ for $m = \min A$.

The source states the equality case only in the direction that equality forces this form; the
converse is included here.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 10. -/
public theorem_wanted card_restrictedSignedSumset_four_five_ge
    (A : Finset ℤ) (hcard : A.card = 5) (hpos : ∀ a ∈ A, 0 < a) :
    ((restrictedSignedSumset 4 A).card : ℤ) ≥ 25 ∧
    (((restrictedSignedSumset 4 A).card : ℤ) = 25 ↔
      ∃ m ∈ A, (∀ a ∈ A, m ≤ a) ∧ A = scaleFinset m (oddProgression 5))

/-- **Lower bound for restricted signed 4-fold sumsets of nonnegative sets containing zero.**
Let $k \ge 5$, let $A$ be a set of $k$ nonnegative integers with $0 \in A$, and write
$4^{\wedge}_{\pm} A$ for the restricted signed 4-fold sumset of $A$. Then
$|4^{\wedge}_{\pm} A| \ge 8k - 19$.

The inverse statement of the source, that equality forces $A = d \cdot \{0, 1, \dots, k - 1\}$
for some integer $d$ (where $d \cdot B = \{db : b \in B\}$), is omitted: $A = \{0, 1, 2, 4, 6\}$
has $|4^{\wedge}_{\pm} A| = 21 = 8 \cdot 5 - 19$ but is not of that form.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 11. -/
public theorem_wanted card_restrictedSignedSumset_four_nonnegative_ge
    (k : ℕ) (A : Finset ℤ) (hk : 5 ≤ k) (hcard : A.card = k)
    (hnonneg : ∀ a ∈ A, 0 ≤ a) (hzero : 0 ∈ A) :
    ((restrictedSignedSumset 4 A).card : ℤ) ≥ 8 * (k : ℤ) - 19

/-- **Extending a restricted signed sumset bound from the first $h+1$ elements.** Let $h \ge 3$
and $k \ge h + 1$, let $a_1 < a_2 < \dots < a_k$ be positive integers, and let $t \ge 0$ be an
integer. Put $A = \{a_1, \dots, a_k\}$ and $A_{h+1} = \{a_1, \dots, a_{h+1}\}$, and write
$h^{\wedge}_{\pm} B$ for the restricted signed $h$-fold sumset of a finite set $B$. If
$|h^{\wedge}_{\pm} A_{h+1}| \ge (h+1)^2 + t$, then $|h^{\wedge}_{\pm} A| \ge 2hk - h^2 + 1 + t$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 1. -/
public theorem_wanted card_restrictedSignedSumset_ge_of_initialSegment
    (h k : ℕ) (hh : 3 ≤ h) (hk : h ≤ k - 1) (a : Fin k → ℤ) (t : ℤ)
    (ha : StrictMono a) (hpos : ∀ i, 0 < a i) (ht : 0 ≤ t)
    (hinitial : ((restrictedSignedSumset h (initialSegment a (h + 1))).card : ℤ) ≥
      ((h + 1 : ℕ) : ℤ) ^ 2 + t) :
    ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≥
      2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 1 + t

/-- **Restricted signed 4-fold sumsets when exactly one gap differs from twice the minimum.**
Let $a_1 < a_2 < a_3 < a_4 < a_5$ be integers with $a_1 > 0$, let $A = \{a_1, \dots, a_5\}$,
and write $4^{\wedge}_{\pm} A$ for the restricted signed 4-fold sumset of $A$. If exactly one
of the four gaps $a_{i+1} - a_i$ with $i \in \{1, 2, 3, 4\}$ differs from $2a_1$, then
$|4^{\wedge}_{\pm} A| \ge 26$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 3. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_one_exceptional_gap
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hgaps : (Finset.univ.filter fun i : Fin 4 =>
      a i.succ - a i.castSucc ≠ 2 * a 0).card = 1) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

/-- **Restricted signed fourfold sumsets when exactly two gaps differ from twice the least
element.** Let $a_1 < a_2 < a_3 < a_4 < a_5$ be integers with $a_1 > 0$, let
$A = \{a_1, \ldots, a_5\}$ and let $4^{\wedge}_{\pm} A$ be the restricted signed sumset of $A$. If
exactly two of the four gaps $a_{i+1} - a_i$ ($1 \le i \le 4$) differ from $2a_1$, then
$|4^{\wedge}_{\pm} A| \ge 26$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 4. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_two_exceptional_gaps
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hgaps : (Finset.univ.filter fun i : Fin 4 =>
      a i.succ - a i.castSucc ≠ 2 * a 0).card = 2) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

/-- **Restricted signed fourfold sumsets when exactly one gap equals twice the least element.**
Let $a_1 < a_2 < a_3 < a_4 < a_5$ be integers with $a_1 > 0$, let $A = \{a_1, \ldots, a_5\}$ and
let $4^{\wedge}_{\pm} A$ be the restricted signed sumset of $A$. If exactly one of the four gaps
$a_{i+1} - a_i$ ($1 \le i \le 4$) equals $2a_1$, then $|4^{\wedge}_{\pm} A| \ge 26$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 5. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_one_regular_gap
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hgaps : (Finset.univ.filter fun i : Fin 4 =>
      a i.succ - a i.castSucc = 2 * a 0).card = 1) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

/-- **Restricted signed fourfold sumsets when no gap equals twice the least element and the first
and third gaps differ.** Let $a_1 < a_2 < a_3 < a_4 < a_5$ be integers with $a_1 > 0$, let
$A = \{a_1, \ldots, a_5\}$ and let $4^{\wedge}_{\pm} A$ be the restricted signed sumset of $A$. If
none of the four gaps $a_{i+1} - a_i$ ($1 \le i \le 4$) equals $2a_1$ and
$a_4 - a_3 \ne a_2 - a_1$, then $|4^{\wedge}_{\pm} A| \ge 26$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 6. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_unequal_outer_gaps
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hnone : ∀ i : Fin 4, a i.succ - a i.castSucc ≠ 2 * a 0)
    (hneq : a 3 - a 2 ≠ a 1 - a 0) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

/-- **Restricted signed fourfold sumsets when no gap equals twice the least element, the first and
third gaps agree, and the last two gaps do not sum to twice the least element.** Let
$a_1 < a_2 < a_3 < a_4 < a_5$ be integers with $a_1 > 0$, let $A = \{a_1, \ldots, a_5\}$ and let
$4^{\wedge}_{\pm} A$ be the restricted signed sumset of $A$. If none of the four gaps
$a_{i+1} - a_i$ ($1 \le i \le 4$) equals $2a_1$, $a_4 - a_3 = a_2 - a_1$ and
$a_5 - a_3 \ne 2a_1$, then $|4^{\wedge}_{\pm} A| \ge 26$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 7. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_equal_outer_gaps_ne
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hnone : ∀ i : Fin 4, a i.succ - a i.castSucc ≠ 2 * a 0)
    (heq : a 3 - a 2 = a 1 - a 0) (hneq : a 4 - a 2 ≠ 2 * a 0) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

/-- **Restricted signed fourfold sumsets when no gap equals twice the least element, the first and
third gaps agree, and the last two gaps sum to twice the least element.** Let
$a_1 < a_2 < a_3 < a_4 < a_5$ be integers with $a_1 > 0$, let $A = \{a_1, \ldots, a_5\}$ and let
$4^{\wedge}_{\pm} A$ be the restricted signed sumset of $A$. If none of the four gaps
$a_{i+1} - a_i$ ($1 \le i \le 4$) equals $2a_1$, $a_4 - a_3 = a_2 - a_1$ and
$a_5 - a_3 = 2a_1$, then $|4^{\wedge}_{\pm} A| \ge 26$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 8. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_equal_outer_gaps_eq
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hnone : ∀ i : Fin 4, a i.succ - a i.castSucc ≠ 2 * a 0)
    (heq : a 3 - a 2 = a 1 - a 0) (hsum : a 4 - a 2 = 2 * a 0) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

/-- **Restricted signed 4-fold sumsets when no gap equals twice the minimum.** Let
$a_1 < a_2 < a_3 < a_4 < a_5$ be integers with $a_1 > 0$, let $A = \{a_1, \dots, a_5\}$, and
write $4^{\wedge}_{\pm} A$ for the restricted signed 4-fold sumset of $A$. If
$a_{i+1} - a_i \ne 2a_1$ for every $i \in \{1, 2, 3, 4\}$, then $|4^{\wedge}_{\pm} A| \ge 26$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 9. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_no_regular_gap
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hnone : ∀ i : Fin 4, a i.succ - a i.castSucc ≠ 2 * a 0) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

end

end MetaMathlibExt
