/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.NoncrossingPartition.Pairing
public import MathlibExt.Probability.Distributions.SemicircleNoncrossingPairings

/-!
# Tests for the Catalan count of noncrossing pair partitions

Concrete counts (including the degenerate arities `0` and odd `n`), an explicit noncrossing
matching, a crossing matching that is rejected, and the semicircle moment bridge.
-/

open NoncrossingPartition

namespace MathlibExtTest.Combinatorics.NoncrossingPartition.Pairing

/-- The empty set has exactly one (empty) pair partition. -/
example : Fintype.card {P : _root_.NoncrossingPartition 0 // IsPairPartition P.val} = 1 := by
  simpa using card_noncrossing_pairPartition_two_mul 0

/-- Two noncrossing pairings of four points: `{12, 34}` and `{14, 23}`. -/
example : Fintype.card {P : _root_.NoncrossingPartition 4 // IsPairPartition P.val} = 2 := by
  simpa [catalan_two] using card_noncrossing_pairPartition_two_mul 2

/-- Five noncrossing pairings of six points. -/
example : Fintype.card {P : _root_.NoncrossingPartition 6 // IsPairPartition P.val} = 5 := by
  simpa [catalan_three] using card_noncrossing_pairPartition_two_mul 3

/-- No pair partition of three points. -/
example : Fintype.card {P : _root_.NoncrossingPartition 3 // IsPairPartition P.val} = 0 := by
  simpa using card_noncrossing_pairPartition_two_mul_add_one 1

/-- The nested matching `0 ↔ 3`, `1 ↔ 2` is a noncrossing perfect matching of four points. -/
example : IsNCMatching 4 (fun i => if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 1
    else if i = 3 then 0 else i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun a b hab hb => ?_, fun i hi => ?_⟩
  all_goals (try interval_cases i) <;> (try simp_all)
  · split_ifs at hb ⊢ <;> omega
  · split_ifs <;> omega

/-- The crossing matching `0 ↔ 2`, `1 ↔ 3` is rejected. -/
example : ¬ IsNCMatching 4 (fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0
    else if i = 3 then 1 else i) := by
  intro h
  have := h.nested 0 1 (by omega) (by simp)
  simp at this

/-- The recursion at `n + 1 = 4`: `M(4) = M(0) M(2) + M(1) M(1) + M(2) M(0)`. -/
example : Nat.card (NCMatching 4) = 2 := by
  rw [card_ncMatching]; simp [catalan_two]

/-- The fourth semicircle moment, `C_2 = 2`, is the number of noncrossing pairings of four points. -/
example : ∫ x, x ^ 4 ∂ProbabilityTheory.semicircleReal = 2 := by
  rw [ProbabilityTheory.integral_pow_semicircleReal_eq_card_noncrossing_pairPartition]
  have := card_noncrossing_pairPartition_two_mul 2
  simp_all [catalan_two]

end MathlibExtTest.Combinatorics.NoncrossingPartition.Pairing
