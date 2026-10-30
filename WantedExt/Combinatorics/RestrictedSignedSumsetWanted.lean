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

/-- `orderedFinset a` is the finite set enumerated by the indexed sequence `a`; order and
injectivity requirements are supplied separately by the statements that use it.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, notation for ordered finite sets. -/
public def orderedFinset {k : ℕ} (a : Fin k → ℤ) : Finset ℤ :=
  Finset.univ.image a

/-- `initialSegment a n` is the set of values whose zero-based indices are less than `n`;
it formalizes the paper's sets of the first `n` elements of an ordered set.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, notation for initial subsets. -/
public def initialSegment {k : ℕ} (a : Fin k → ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.univ.filter fun i : Fin k => (i : ℕ) < n).image a

/-- `IsIndexedAP a d` says that `a` is an arithmetic progression with positive common
difference `d`: every pair of adjacent zero-based terms differs by `d`. This adjacent-term
form avoids adding a nonemptiness assumption merely to name a first term.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, definition of arithmetic progression. -/
public def IsIndexedAP {k : ℕ} (a : Fin k → ℤ) (d : ℤ) : Prop :=
  0 < d ∧ ∀ (i j : Fin k), (i : ℕ) + 1 = (j : ℕ) → a j = a i + d

/-- `scaleFinset d B` is the dilation `d * B`, with membership values `d*b` for `b ∈ B`.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, dilation notation. -/
public def scaleFinset (d : ℤ) (B : Finset ℤ) : Finset ℤ :=
  B.image (fun b => d * b)

/-- `oddProgression k` is `{1, 3, ..., 2k-1}`, encoded by zero-based indices.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, odd-progression notation. -/
public def oddProgression (k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun i : ℕ => 2 * (i : ℤ) + 1)

/-- `tailFinset a` removes the first, zero-indexed term from the finite set enumerated by
`a`; under `StrictMono a` this is the paper's `A'`.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, notation `A'`. -/
public def tailFinset {k : ℕ} (a : Fin k → ℤ) : Finset ℤ :=
  (Finset.univ.filter fun i : Fin k => 0 < (i : ℕ)).image a

/-- `zeroInterval k` is the integer set `{0,1,...,k-1}`, the paper's interval `[0,k-1]`.
The zero-based range encoding avoids any ambiguity from integer interval endpoints.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, interval notation. -/
public def zeroInterval (k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun i : ℕ => (i : ℤ))

/-- The restricted signed four-fold sumset of `{1,3,5,7,9}` has cardinality `25`.
This is the extremal positive five-element example used in Theorem 10.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 10 example. -/
public theorem card_restrictedSignedSumset_four_odd_five :
    (restrictedSignedSumset 4 {1, 3, 5, 7, 9}).card = 25 := by
  decide +kernel

/-- The restricted signed four-fold sumset of `{0,1,2,4,6}` has cardinality `21 = 8·5 - 19`,
the extremal value of Theorem 11. Together with `ne_scaleFinset_zeroInterval_five` this
refutes the inverse sentence of Theorem 11 (the counterexample is ours, not the paper's).
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 11 (lower bound `8k - 19` at `k = 5`). -/
public theorem card_restrictedSignedSumset_four_counterexample :
    (restrictedSignedSumset 4 {0, 1, 2, 4, 6}).card = 21 := by
  decide +kernel

/-- `{0,1,2,4,6}` is not a dilated interval `d * [0,4]`: `1` forces `d = ±1`, and then `6` is
out of reach.
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

/-- The restricted signed three-fold sumset of `{1,2,3,4}` has cardinality `19`; the
numeral is the computed value requested as a small executable check.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Definition of restricted signed sumset. -/
public theorem card_restrictedSignedSumset_three_four :
    (restrictedSignedSumset 3 {1, 2, 3, 4}).card = 19 := by
  decide

/-- For positive `h ≤ k` and a `k`-element finset `A` of nonnegative integers, the two
implications formalize respectively the cases `0 ∉ A` and `0 ∈ A`. Both paper bounds are
multiplied by `2` to avoid integer division. The trailing optimality remark for `h=1,2,k`
is omitted as requested.
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

/-- The first conjunct is Nathanson's lower bound for every nonempty finite integer set
with `1 ≤ h ≤ |A|`. The second is the inverse clause: under `|A| ≥ 5`,
`2 ≤ h ≤ |A|-2`, equality holds if and only if `A` is an arithmetic progression, expressed
by `0 < d ∧ (A : Set ℤ).IsAPOfLengthWith A.card a d`.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 2. -/
public theorem_wanted card_restrictedSumset_ge_and_eq_iff_ap
    (h : ℕ) (A : Finset ℤ) (hA : A.Nonempty) (hh : 1 ≤ h) (hhA : h ≤ A.card) :
    ((restrictedSumset h A).card : ℤ) ≥ (h : ℤ) * A.card - (h : ℤ) ^ 2 + 1 ∧
    (5 ≤ A.card → 2 ≤ h → h ≤ A.card - 2 →
      (((restrictedSumset h A).card : ℤ) = (h : ℤ) * A.card - (h : ℤ) ^ 2 + 1 ↔
        ∃ a d : ℤ, 0 < d ∧ (A : Set ℤ).IsAPOfLengthWith A.card a d))

/-- For `h ≥ 3`, `a` enumerates the `h+1` positive terms increasingly and
`IsIndexedAP a d` gives the positive common difference. The first conjunct chooses the
paper's bound according as `d = 2*a₁`; the second is the equality characterization.
The minimum is represented by the first term `a 0`, using strict monotonicity.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 3. -/
public theorem_wanted card_restrictedSignedSumset_ap_h_add_one
    (h : ℕ) (hh : 3 ≤ h) (a : Fin (h + 1) → ℤ) (d : ℤ)
    (ha : StrictMono a) (hpos : ∀ i, 0 < a i) (hap : IsIndexedAP a d) :
    (((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≥
      if d = 2 * a ⟨0, by omega⟩ then ((h + 1 : ℕ) : ℤ) ^ 2
      else ((h + 1 : ℕ) : ℤ) ^ 2 + 1) ∧
    (((restrictedSignedSumset h (orderedFinset a)).card : ℤ) =
        ((h + 1 : ℕ) : ℤ) ^ 2 ↔ d = 2 * a ⟨0, by omega⟩)

/-- Here `a : Fin k → ℤ` formalizes `A={a₁<⋯<aₖ}`, `h+1 ≤ k` is the length
condition, and `IsIndexedAP a d` supplies the common difference. The conditional lower
bound and equality iff clause are exactly the corollary's two conclusions; `a 0` is
`min(A)`. No clause is omitted.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Corollary 1. -/
public theorem_wanted card_restrictedSignedSumset_ap_ge
    (h k : ℕ) (hh : 3 ≤ h) (hk : h + 1 ≤ k) (a : Fin k → ℤ) (d : ℤ)
    (ha : StrictMono a) (hpos : 0 < a ⟨0, by omega⟩) (hap : IsIndexedAP a d) :
    (((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≥
      if d = 2 * a ⟨0, by omega⟩ then 2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 1
      else 2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 2) ∧
    (((restrictedSignedSumset h (orderedFinset a)).card : ℤ) =
        2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 1 ↔ d = 2 * a ⟨0, by omega⟩)

/-- For `4 ≤ h ≤ k-1`, `a` increasingly enumerates the nonnegative progression,
`a 0 = 0` encodes `0 ∈ A`, and `IsIndexedAP a d` records its common difference. The
displayed integer equality is the paper's exact cardinality formula without deviation.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 4. -/
public theorem_wanted card_restrictedSignedSumset_ap_zero
    (h k : ℕ) (hh : 4 ≤ h) (hk : h ≤ k - 1) (a : Fin k → ℤ) (d : ℤ)
    (ha : StrictMono a) (hnonneg : ∀ i, 0 ≤ a i)
    (hzero : a ⟨0, by omega⟩ = 0) (hap : IsIndexedAP a d) :
    ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) =
      2 * (h : ℤ) * k - (h : ℤ) * (h + 1) + 1

/-- `a` encodes the `k` positive integers increasingly; `initialSegment a (h+1)` is
`A_{h+1}` and `tailFinset a` is `A'`. The cardinality equality is the extremal hypothesis,
and the five disjuncts reproduce cases (a)–(e), including the union in (d). The conclusion
uses `scaleFinset` and `oddProgression` for `a₁*{1,3,…,2k-1}`.
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

/-- `a` encodes `A={a₀<⋯<a_{k-1}}`, with nonnegative terms and `a₀=0`;
`initialSegment a (h+1)` is the paper's `A_h` (indices `0,…,h`) and `tailFinset a` is
`A'`. The extremal equality and five disjuncts are cases (a)–(e). The conclusion encodes
`a₁*[0,k-1]` using `zeroInterval`; no condition is added or omitted.
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

/-- For `h ≥ 3`, `a` is a strictly increasing positive sequence of `h+1` terms. The
quantification over `i : Fin (h-2)` represents paper indices `4,…,h+1`, and the displayed
inequality is `a_i ≥ a_{i-1}+a_{i-2}` after converting to zero-based indices. The
conclusion is the stated `(h+1)^2+1` lower bound.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 7. -/
public theorem_wanted card_restrictedSignedSumset_ge_of_fibonacci_growth
    (h : ℕ) (hh : 3 ≤ h) (a : Fin (h + 1) → ℤ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i)
    (hgrowth : ∀ i : Fin (h - 2),
      a ⟨i + 3, by omega⟩ ≥ a ⟨i + 2, by omega⟩ + a ⟨i + 1, by omega⟩) :
    ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≥
      ((h + 1 : ℕ) : ℤ) ^ 2 + 1

/-- For `h ≥ 3`, the first gap hypothesis is `a₃-a₂ < 2a₁`. For every paper index
`i=4,…,h+1`, represented by `Fin (h-2)`, the second hypothesis is written without
division as `a₂-a₁ < 2*(a_i-a_{i-1})`, exactly the requested encoding. The conclusion is
the paper's lower bound.
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

/-- For a `k`-element set of positive integers with `k ≥ 5`, the conjunction states the
`8k-15` lower bound and its equality case as an `↔`: the paper prints the inverse
direction, and the converse (every `m*{1,3,…,2k-1}` attains `8k-15`) is included. The existential `m` is explicitly required to
belong to `A` and be no larger than every member, so it is exactly `min(A)` without a
proof-valued `min'` argument; the conclusion is `m*{1,3,…,2k-1}`. The hypothesis
`5 ≤ k` is the paper's own: Theorem 9 is stated for `k ≥ 5`, and the paper proves it from
its five-element base case Theorem 10 via Lemma 1 and Theorem 5, so Theorem 10 below is
the `k = 5` specialization of this statement rather than a separate case.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 9. -/
public theorem_wanted card_restrictedSignedSumset_four_ge
    (k : ℕ) (A : Finset ℤ) (hk : 5 ≤ k) (hcard : A.card = k)
    (hpos : ∀ a ∈ A, 0 < a) :
    ((restrictedSignedSumset 4 A).card : ℤ) ≥ 8 * (k : ℤ) - 15 ∧
    (((restrictedSignedSumset 4 A).card : ℤ) = 8 * (k : ℤ) - 15 ↔
      ∃ m ∈ A, (∀ a ∈ A, m ≤ a) ∧ A = scaleFinset m (oddProgression k))

/-- For a five-element set `A` of positive integers, the conjunction states the lower
bound `25` and the equality classification as an `↔` (the paper prints the inverse
direction; `m*{1,3,5,7,9}` attains `25`). The existential `m` is explicitly the minimum
of `A`; `{1,3,5,7,9}` is represented by `oddProgression 5`.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 10. -/
public theorem_wanted card_restrictedSignedSumset_four_five_ge
    (A : Finset ℤ) (hcard : A.card = 5) (hpos : ∀ a ∈ A, 0 < a) :
    ((restrictedSignedSumset 4 A).card : ℤ) ≥ 25 ∧
    (((restrictedSignedSumset 4 A).card : ℤ) = 25 ↔
      ∃ m ∈ A, (∀ a ∈ A, m ≤ a) ∧ A = scaleFinset m (oddProgression 5))

/-- For a `k`-element set of nonnegative integers containing zero, this states only the
paper's lower bound `8k-19`. The inverse sentence is deliberately omitted: at `k=5`,
`A={0,1,2,4,6}` has cardinality `21=8*5-19` but is not a dilated interval, as witnessed
by `card_restrictedSignedSumset_four_counterexample` and `ne_scaleFinset_zeroInterval_five`
above.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 11. -/
public theorem_wanted card_restrictedSignedSumset_four_nonnegative_ge
    (k : ℕ) (A : Finset ℤ) (hk : 5 ≤ k) (hcard : A.card = k)
    (hnonneg : ∀ a ∈ A, 0 ≤ a) (hzero : 0 ∈ A) :
    ((restrictedSignedSumset 4 A).card : ℤ) ≥ 8 * (k : ℤ) - 19

/-- `a` increasingly enumerates the positive `k`-element set and
`initialSegment a (h+1)` is `A_{h+1}`. From its lower bound by `(h+1)^2+t`, with
integer `t ≥ 0`, the conclusion gives the paper's bound for all of `A`. The paper leaves
the type of `t` implicit; it is represented as an integer to match cardinality arithmetic.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 1. -/
public theorem_wanted card_restrictedSignedSumset_ge_of_initialSegment
    (h k : ℕ) (hh : 3 ≤ h) (hk : h ≤ k - 1) (a : Fin k → ℤ) (t : ℤ)
    (ha : StrictMono a) (hpos : ∀ i, 0 < a i) (ht : 0 ≤ t)
    (hinitial : ((restrictedSignedSumset h (initialSegment a (h + 1))).card : ℤ) ≥
      ((h + 1 : ℕ) : ℤ) ^ 2 + t) :
    ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≥
      2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 1 + t

/-- For the five positive terms enumerated increasingly by `a`, the filtered-cardinality
hypothesis says exactly one of the four successive gaps differs from `2*a₁`; hence the
other three equal it. The conclusion is `|4^∧_±A| ≥ 26`.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 3. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_one_exceptional_gap
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hgaps : (Finset.univ.filter fun i : Fin 4 =>
      a i.succ - a i.castSucc ≠ 2 * a 0).card = 1) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

/-- For the five positive increasing terms, the filtered-cardinality hypothesis says
exactly two successive gaps differ from `2*a₁` and therefore the remaining two equal it.
The conclusion is the paper's `26` lower bound.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 4. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_two_exceptional_gaps
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hgaps : (Finset.univ.filter fun i : Fin 4 =>
      a i.succ - a i.castSucc ≠ 2 * a 0).card = 2) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

/-- For the five positive increasing terms, the filtered-cardinality hypothesis says
exactly one successive gap equals `2*a₁` and the other three do not. The conclusion is
the paper's `26` lower bound.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 5. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_one_regular_gap
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hgaps : (Finset.univ.filter fun i : Fin 4 =>
      a i.succ - a i.castSucc = 2 * a 0).card = 1) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

/-- All four successive gaps differ from `2*a₁`, and the additional displayed hypothesis
is `a₄-a₃ ≠ a₂-a₁` in one-based paper indices. With `a` positive and strictly increasing,
the conclusion is `|4^∧_±A| ≥ 26`.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 6. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_unequal_outer_gaps
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hnone : ∀ i : Fin 4, a i.succ - a i.castSucc ≠ 2 * a 0)
    (hneq : a 3 - a 2 ≠ a 1 - a 0) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

/-- All successive gaps differ from `2*a₁`; additionally `a₄-a₃=a₂-a₁` and
`a₅-a₃ ≠ 2*a₁`, with numerals interpreted through the zero-based `Fin 5` encoding.
The conclusion is the paper's `26` lower bound.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 7. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_equal_outer_gaps_ne
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hnone : ∀ i : Fin 4, a i.succ - a i.castSucc ≠ 2 * a 0)
    (heq : a 3 - a 2 = a 1 - a 0) (hneq : a 4 - a 2 ≠ 2 * a 0) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

/-- All successive gaps differ from `2*a₁`; additionally `a₄-a₃=a₂-a₁` and
`a₅-a₃=2*a₁`, using zero-based indices in `Fin 5`. The conclusion is the stated
`|4^∧_±A| ≥ 26`.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 8. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_equal_outer_gaps_eq
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hnone : ∀ i : Fin 4, a i.succ - a i.castSucc ≠ 2 * a 0)
    (heq : a 3 - a 2 = a 1 - a 0) (hsum : a 4 - a 2 = 2 * a 0) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

/-- For the five positive increasing terms, every successive gap differs from `2*a₁`.
This is exactly the sole additional hypothesis of Lemma 9, and the conclusion is the
paper's `26` lower bound.
Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Lemma 9. -/
public theorem_wanted card_restrictedSignedSumset_four_ge_of_no_regular_gap
    (a : Fin 5 → ℤ) (ha : StrictMono a) (hpos : 0 < a 0)
    (hnone : ∀ i : Fin 4, a i.succ - a i.castSucc ≠ 2 * a 0) :
    ((restrictedSignedSumset 4 (orderedFinset a)).card : ℤ) ≥ 26

end

end MetaMathlibExt
