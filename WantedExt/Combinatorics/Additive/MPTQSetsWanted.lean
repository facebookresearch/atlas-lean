/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Coprime.Basic
public import MathlibExt.Combinatorics.Additive.MPTQSets
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

/-- **Hegarty: no seven-element MSTD set of integers.** No set of seven integers, viewed as a set
of real numbers, is an MSTD set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 1 (`integers-2024-A96-thm-1`). -/
public theorem_wanted not_isMSTDSet_int_of_card_eq_seven (A : Finset ℤ) (hA : A.card = 7) :
    ¬ IsMSTDSet (A.image ((↑) : ℤ → ℝ))

/-- **Hegarty's classification of MSTD sets of size eight.** Let $A$ be a set of eight integers,
regarded as a set of real numbers, and let $S = \{0, 2, 3, 4, 7, 11, 12, 14\}$. Then $A$ is an
MSTD set if and only if $A = \{as + b : s \in S\}$ for some integers $a \neq 0$ and $b$.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 1 (`integers-2024-A96-thm-1`). -/
public theorem_wanted isMSTDSet_int_of_card_eq_eight_iff (A : Finset ℤ) (hA : A.card = 8) :
    IsMSTDSet (A.image ((↑) : ℤ → ℝ)) ↔
      ∃ a b : ℤ, a ≠ 0 ∧ A = ({0, 2, 3, 4, 7, 11, 12, 14} : Finset ℤ).image (fun s => a * s + b)

/-- **Chu's bound for MPTQ sets of positive reals.** Every MPTQ set whose elements are all
positive real numbers has at least $8$ elements.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 2 (`integers-2024-A96-thm-2`). -/
public theorem_wanted eight_le_card_of_isMPTQSet_of_pos {A : Finset ℝ} (hA : IsMPTQSet A)
    (hpos : ∀ a ∈ A, 0 < a) : 8 ≤ A.card

/-- **Chu's bound for MPTQ sets with a negative element.** Every MPTQ set of real numbers that
contains a negative number has at least $5$ elements.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 2 (`integers-2024-A96-thm-2`). -/
public theorem_wanted five_le_card_of_isMPTQSet_of_neg {A : Finset ℝ} (hA : IsMPTQSet A)
    (hneg : ∃ a ∈ A, a < 0) : 5 ≤ A.card

/-- **Five-element sets with one negative element are not MPTQ sets.** If $A$ is a set of five
real numbers exactly one of which is negative, then $A$ is not an MPTQ set.

The source assumes the elements are nonzero; this is not needed, since a set containing $0$ is
never an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 4 (`integers-2024-A96-lem-4`). -/
public theorem_wanted not_isMPTQSet_of_card_five_one_neg {A : Finset ℝ} (hcard : A.card = 5)
    (hneg : (A.filter (· < 0)).card = 1) : ¬ IsMPTQSet A

/-- **Five-element sets with two negative elements are not MPTQ sets.** If $A$ is a set of five
real numbers exactly two of which are negative, then $A$ is not an MPTQ set.

The source assumes the elements are nonzero; this is not needed, since a set containing $0$ is
never an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 5 (`integers-2024-A96-lem-5`). -/
public theorem_wanted not_isMPTQSet_of_card_five_two_neg {A : Finset ℝ} (hcard : A.card = 5)
    (hneg : (A.filter (· < 0)).card = 2) : ¬ IsMPTQSet A

/-- **No MPTQ set has five elements.** No set of five real numbers is an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 3 (`integers-2024-A96-thm-3`). -/
public theorem_wanted not_isMPTQSet_of_card_eq_five {A : Finset ℝ} (hcard : A.card = 5) :
    ¬ IsMPTQSet A

end

end MetaMathlibExt
