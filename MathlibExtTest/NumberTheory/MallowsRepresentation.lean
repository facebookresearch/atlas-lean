/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MallowsRepresentation

open MetaMathlibExt

-- The input starts L, R, L, so Q starts OL, OL, ER, OR.
-- T is L within the first run, then M at its end (the even letter is skipped).
example (x : ℕ → SternBrocotLetter) (h0 : x 0 = .L) (h1 : x 1 = .R) (h2 : x 2 = .L) :
    mallowsT (mallowsQ x) 0 = .L ∧ mallowsT (mallowsQ x) 1 = .M := by
  let p (j : ℕ) := mallowsQ x j = .OL ∨ mallowsQ x j = .OR
  have q0 : mallowsQ x 0 = .OL := rfl
  have q1 : mallowsQ x 1 = .OL := by simp [mallowsQ, mallowsQStep, h0]
  have q2 : mallowsQ x 2 = .ER := by
    change mallowsQStep (mallowsQ x 1) (x 1) = .ER
    rw [q1, h1]
    rfl
  have q3 : mallowsQ x 3 = .OR := by
    change mallowsQStep (mallowsQ x 2) (x 2) = .OR
    rw [q2, h2]
    rfl
  have o0 : mallowsOddIndex (mallowsQ x) 0 = 0 := Nat.nth_zero_of_zero (Or.inl q0)
  have o1 : mallowsOddIndex (mallowsQ x) 1 = 1 := by
    simpa [mallowsOddIndex, p, Nat.count_succ, Nat.count_zero, q0] using
      (Nat.nth_count (p := p) (Or.inl q1))
  have o2 : mallowsOddIndex (mallowsQ x) 2 = 3 := by
    simpa [mallowsOddIndex, p, Nat.count_succ, Nat.count_zero, q0, q1, q2] using
      (Nat.nth_count (p := p) (Or.inr q3))
  simp [mallowsT, mallowsTLetter, o0, o1, o2, q0, q1, q3]

-- Run length two places the first M at Lean index 1, not at index 0.
example (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (hirr : Irrational α)
    (e : ℕ → ℕ) (he : ∀ k, 0 < e k) (he0 : e 0 = 2)
    (hrun : ∀ k i, ∑ t ∈ Finset.range k, e t ≤ i → i < ∑ t ∈ Finset.range (k + 1), e t →
      mallowsQ (sternBrocotRep α) (mallowsOddIndex (mallowsQ (sternBrocotRep α)) i) =
        if Even k then .OL else .OR) :
    mallowsT (mallowsQ (sternBrocotRep α)) 0 ≠ .M ∧
      mallowsT (mallowsQ (sternBrocotRep α)) 1 = .M := by
  constructor
  · intro h
    obtain ⟨k, hk, hsum⟩ :=
      (mallowsT_eq_M_iff_runEnd (hα := hα) (hirr := hirr) α e he hrun 0).mp h
    have hmem : 0 ∈ Finset.range k := Finset.mem_range.mpr hk
    have hle := Finset.single_le_sum (f := e) (fun t _ => Nat.zero_le (e t)) hmem
    omega
  · exact (mallowsT_eq_M_iff_runEnd (hα := hα) (hirr := hirr) α e he hrun 1).mpr
      ⟨1, le_rfl, by simp [he0]⟩
