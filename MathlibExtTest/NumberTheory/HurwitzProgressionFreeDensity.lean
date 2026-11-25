/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HurwitzProgressionFreeDensity

/-! # Tests for the density bound for progression-free Hurwitz sets -/

namespace MathlibExtTest.HurwitzProgressionFreeDensity

private def hurwitz : Set (Quaternion ℚ) := {q |
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) ∧ q.imI = (b : ℚ) ∧ q.imJ = (c : ℚ) ∧ q.imK = (d : ℚ)) ∨
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) + 1 / 2 ∧ q.imI = (b : ℚ) + 1 / 2 ∧
      q.imJ = (c : ℚ) + 1 / 2 ∧ q.imK = (d : ℚ) + 1 / 2)}

private def boundedPoints (N : ℕ) : Set (Quaternion ℚ) :=
  {q ∈ hurwitz | q ≠ 0 ∧ Quaternion.normSq q ≤ (N : ℚ)}

private def halfUnit : Quaternion ℚ := ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩

-- Zero may belong to the set, and the other point uses the half-integral coset.
example :
    let A : Set (Quaternion ℚ) := {0, halfUnit}
    Filter.limsup (fun N : ℕ => ((A ∩ boundedPoints N).ncard : ℝ) / (boundedPoints N).ncard)
      Filter.atTop ≤ 20 / 21 := by
  apply MetaMathlibExt.upperDensity_le_of_hurwitz_gpFree
  constructor
  · intro q hq
    rcases Set.mem_insert_iff.mp hq with rfl | h
    · exact Or.inl ⟨0, 0, 0, 0, by simp⟩
    · rw [Set.mem_singleton_iff.mp h]
      exact Or.inr ⟨0, 0, 0, 0, by simp [halfUnit]⟩
  · rintro a _ r _ ha hr hn ⟨h₀, h₁, _⟩
    have h₀' := (Set.mem_insert_iff.mp h₀).resolve_left ha
    have h₁' := (Set.mem_insert_iff.mp h₁).resolve_left (mul_ne_zero ha hr)
    have he : a * r = a := (Set.mem_singleton_iff.mp h₁').trans (Set.mem_singleton_iff.mp h₀').symm
    exact hn (by rw [mul_left_cancel₀ ha (he.trans (mul_one a).symm), map_one])

end MathlibExtTest.HurwitzProgressionFreeDensity
