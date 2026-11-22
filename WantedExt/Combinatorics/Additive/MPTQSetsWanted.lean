/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Coprime.Basic
public import WantedExt.Combinatorics.Additive.UnionTwoAPNotMSTDWanted

/-!
# The minimum cardinality of MPTQ sets

Statements from Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96.

For a finite set `A ⊆ ℝ ∖ {0}`, `A.A = {a a'}` and `A/A = {a / a'}`; `A` is an MPTQ (more
products than quotients) set when `|A.A| > |A/A|`. Integer sets are viewed as sets of reals.
MSTD sets reuse `IsMSTDSet`.
-/

namespace MetaMathlibExt

open Pointwise

@[expose] public section

/-- A finite set of reals is an MPTQ (more products than quotients) set when it avoids `0`
and `|A/A| < |A.A|`.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Definition 1. -/
def IsMPTQSet (A : Finset ℝ) : Prop :=
  (0 : ℝ) ∉ A ∧ (A / A).card < (A * A).card

/-- A singleton is not an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Definition 1. -/
theorem not_isMPTQSet_singleton (a : ℝ) : ¬ IsMPTQSet {a} := by
  simp [IsMPTQSet]

/-- A set containing `0` is not an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Definition 1. -/
theorem not_isMPTQSet_of_zero_mem {A : Finset ℝ} (h : (0 : ℝ) ∈ A) : ¬ IsMPTQSet A :=
  fun hA => hA.1 h

/-- Theorem 1 (quoting Hegarty), size 7: no set of seven integers is an MSTD set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 1 (`integers-2024-A96-thm-1`). -/
public theorem_wanted not_isMSTDSet_int_of_card_eq_seven (A : Finset ℤ) (hA : A.card = 7) :
    ¬ IsMSTDSet (A.image ((↑) : ℤ → ℝ))

/-- Theorem 1 (quoting Hegarty), size 8: a set of eight integers is an MSTD set exactly when
it is an affine image `a S + b` (`a ≠ 0`) of `S = {0, 2, 3, 4, 7, 11, 12, 14}`.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 1 (`integers-2024-A96-thm-1`). -/
public theorem_wanted isMSTDSet_int_of_card_eq_eight_iff (A : Finset ℤ) (hA : A.card = 8) :
    IsMSTDSet (A.image ((↑) : ℤ → ℝ)) ↔
      ∃ a b : ℤ, a ≠ 0 ∧ A = ({0, 2, 3, 4, 7, 11, 12, 14} : Finset ℤ).image (fun s => a * s + b)

/-- Theorem 2 (quoting Chu), part 1: an MPTQ set of positive reals has at least 8 elements.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 2 (`integers-2024-A96-thm-2`). -/
public theorem_wanted eight_le_card_of_isMPTQSet_of_pos {A : Finset ℝ} (hA : IsMPTQSet A)
    (hpos : ∀ a ∈ A, 0 < a) : 8 ≤ A.card

/-- Theorem 2 (quoting Chu), part 2: an MPTQ set of reals containing a negative number has at
least 5 elements.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 2 (`integers-2024-A96-thm-2`). -/
public theorem_wanted five_le_card_of_isMPTQSet_of_neg {A : Finset ℝ} (hA : IsMPTQSet A)
    (hneg : ∃ a ∈ A, a < 0) : 5 ≤ A.card

/-- Lemma 1: if `A` is not an MPTQ set and adjoining `x` adds at most `n` products and at
least `m` quotients, with `n ≤ m`, then `A ∪ {x}` is not an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 1 (`integers-2024-A96-lem-1`). -/
public theorem_wanted not_isMPTQSet_insert_of_le {A : Finset ℝ} {x : ℝ} {n m : ℕ}
    (hA : ¬ IsMPTQSet A) (hn : (insert x A * insert x A).card ≤ (A * A).card + n)
    (hm : (A / A).card + m ≤ (insert x A / insert x A).card) (hnm : n ≤ m) :
    ¬ IsMPTQSet (insert x A)

/-- Lemma 2: if `a, b, c, d` are distinct positive reals with `ab = cd`, then neither
`ad = bc` nor `ac = bd`.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 2 (`integers-2024-A96-lem-2`). -/
public theorem_wanted mul_ne_of_mul_eq_of_distinct {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (h : a * b = c * d) : a * d ≠ b * c ∧ a * c ≠ b * d

/-- Lemma 3: for distinct positive reals `a, b, c`, at most one of `a^2 = bc`, `b^2 = ac`,
`c^2 = ab` holds (in particular not all three).

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 3 (`integers-2024-A96-lem-3`). -/
public theorem_wanted at_most_one_sq_eq_mul_of_distinct {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ (a ^ 2 = b * c ∧ b ^ 2 = a * c) ∧ ¬ (a ^ 2 = b * c ∧ c ^ 2 = a * b) ∧
      ¬ (b ^ 2 = a * c ∧ c ^ 2 = a * b)

/-- Lemma 4: a set of five nonzero reals with exactly one negative element is not an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 4 (`integers-2024-A96-lem-4`). -/
public theorem_wanted not_isMPTQSet_of_card_five_one_neg {A : Finset ℝ} (hcard : A.card = 5)
    (hneg : (A.filter (· < 0)).card = 1) : ¬ IsMPTQSet A

/-- Lemma 5: a set of five nonzero reals with exactly two negative elements is not an MPTQ
set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 5 (`integers-2024-A96-lem-5`). -/
public theorem_wanted not_isMPTQSet_of_card_five_two_neg {A : Finset ℝ} (hcard : A.card = 5)
    (hneg : (A.filter (· < 0)).card = 2) : ¬ IsMPTQSet A

/-- Proposition 1: a finite set `A` of positive reals is an MPTQ set if and only if
`A ∪ (-A)` is.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Proposition 1 (`integers-2024-A96-prop-1`). -/
public theorem_wanted isMPTQSet_union_neg_iff {A : Finset ℝ} (hpos : ∀ a ∈ A, 0 < a) :
    IsMPTQSet (A ∪ -A) ↔ IsMPTQSet A

/-- Theorem 3: no set of five reals is an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 3 (`integers-2024-A96-thm-3`). -/
public theorem_wanted not_isMPTQSet_of_card_eq_five {A : Finset ℝ} (hcard : A.card = 5) :
    ¬ IsMPTQSet A

/-- Theorem 4: for a finite set `A` of integers and a prime `p` coprime to every element of
`A`, `A` is an MPTQ set if and only if `A ∪ pA` is.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 4 (`integers-2024-A96-thm-4`). -/
public theorem_wanted isMPTQSet_union_prime_mul_iff (A : Finset ℤ) {p : ℕ} (hp : p.Prime)
    (hcop : ∀ a ∈ A, IsCoprime a (p : ℤ)) :
    IsMPTQSet ((A ∪ A.image ((p : ℤ) * ·)).image ((↑) : ℤ → ℝ)) ↔
      IsMPTQSet (A.image ((↑) : ℤ → ℝ))

end

end MetaMathlibExt
