/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.AcceleratedZeckendorfGame

/-! # Tests for the Accelerated Zeckendorf Game -/

namespace MetaMathlibExt.accelZeckMove_fib_combine

open Finsupp

-- At the smallest indices, one pair combines and both input piles are exhausted.
example : AccelZeckMove (single 2 1 + single 1 1) (single 3 1) := by
  have h := (accelZeckMove_fib_combine 2 1 (by decide) (by decide)
    (single 2 1 + single 1 1) (by simp) (by simp) (by simp)).1
  change AccelZeckMove _ ((single 2 1 + single 1 1) - single 1 1 - single 2 1 + single 3 1) at h
  simpa using h

-- Two pairs combine at once, leaving one copy at the middle index.
example : AccelZeckMove (single 2 3 + single 1 2) (single 2 1 + single 3 2) := by
  have h := (accelZeckMove_fib_combine 2 3 (by decide) (by decide)
    (single 2 3 + single 1 2) (by simp [Nat.fib_add_two])
    (by simp [Nat.fib_add_two]) (by simp)).1
  change AccelZeckMove _ ((single 2 3 + single 1 2 - single 1 2) - single 2 2 + single 3 2) at h
  simpa [← single_tsub] using h

end MetaMathlibExt.accelZeckMove_fib_combine

namespace MetaMathlibExt

-- Apply the implication at the first starting size covered by Conjecture 1.6.
example (h17 : ∀ n, AccelZeckLosing (Finsupp.single 1 n) → ∀ k, 3 * k ≤ n →
    AccelZeckLosing (Finsupp.single 3 k + Finsupp.single 1 (n - 3 * k))) :
    AccelZeckWinning (Finsupp.single 1 10) :=
  accelZeck_conjecture17_implies_conjecture16 (h17 := h17) 10 (by decide)

end MetaMathlibExt

namespace MetaMathlibExt.accelZeck_odd_unique_losing_move

open Finsupp

-- At n = 3k with k = 1, the hypotheses hold and the unique losing move exhausts both piles.
example : AccelZeckMove (single 2 1 + single 1 1) (single 3 1) ∧
    AccelZeckLosing (single 3 1) ∧
    ∀ t, AccelZeckMove (single 2 1 + single 1 1) t → AccelZeckLosing t → t = single 3 1 := by
  have hterminal : AccelZeckLosing (single 3 1) := by
    apply accelZeckLosing_of_terminal
    rintro t ⟨m, hm, ⟨i, hi, h₁, h₂, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨i, hi, h, -⟩⟩
    · simp only [single_apply] at h₁ h₂
      split_ifs at h₁ h₂ <;> omega
    · simp at h; omega
    · simp at h; omega
    · simp only [single_apply] at h
      split_ifs at h <;> omega
  have hnext : AccelZeckWinning (single 2 1 + single 1 1) := by
    refine .intro _ _ ⟨1, by decide, Or.inl ⟨2, by decide, by simp, by simp, ?_⟩⟩ hterminal
    ext i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, single_apply]
    split_ifs <;> omega
  have hstart : AccelZeckLosing (single 1 3) := by
    refine .intro _ ?_
    rintro t ⟨m, hm, ⟨i, hi, -, h, -⟩ | ⟨h, rfl⟩ | ⟨h, -⟩ | ⟨i, hi, h, -⟩⟩
    · simp only [single_apply] at h
      split_ifs at h <;> omega
    · have hm₁ : 2 * m ≤ 3 := by simpa using h
      obtain rfl : m = 1 := by omega
      simpa [← single_tsub, add_comm] using hnext
    · simp at h; omega
    · simp only [single_apply] at h
      split_ifs at h <;> omega
  have h := accelZeck_odd_unique_losing_move 1 3 (by decide) (by decide) (by
    intro i hi _
    obtain rfl : i = 0 := by omega
    simpa using hstart)
  simpa using h.2

-- At n = 2k with k = 1, the smaller-pile losing hypothesis is impossible.
example : ¬ AccelZeckLosing (single 1 2) := by
  intro hstart
  have h := accelZeck_odd_unique_losing_move 1 2 (by decide) (by decide) (by
    intro i hi _
    obtain rfl : i = 0 := by omega
    simpa using hstart)
  have hbound := h.1
  omega

-- Splitting at k = 3 can consume two twos, but the remaining two rules out a losing successor.
example (hlose : ∀ i < 3, 3 * i ≤ 9 → AccelZeckLosing (single 3 i + single 1 (9 - 3 * i))) :
    ¬ AccelZeckLosing (single 1 4 + single 2 1 + single 3 1) := by
  intro hl
  have hsplit : AccelZeckMove (single 2 3 + single 1 3) (single 1 4 + single 2 1 + single 3 1) := by
    refine ⟨1, by decide, Or.inr (Or.inr (Or.inl ⟨by simp, ?_⟩))⟩
    ext i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, single_apply]
    split_ifs <;> omega
  have h := accelZeck_odd_unique_losing_move 3 9 (by decide) (by decide) hlose
  have heq := h.2.2.2 _ (by simpa using hsplit) hl
  have htwo := congrArg (fun s : ℕ →₀ ℕ => s 2) heq
  simp at htwo

end MetaMathlibExt.accelZeck_odd_unique_losing_move
