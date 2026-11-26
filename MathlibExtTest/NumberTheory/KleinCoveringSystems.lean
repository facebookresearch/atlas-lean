/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.KleinCoveringSystems

/-! # Tests for replacing the largest prime factor of a covering system's moduli -/

namespace MathlibExtTest.NumberTheory.KleinCoveringSystems

/-- The prime divisors of `10` are at most `5`. -/
private theorem prime_dvd_10_le_five (r : ℕ) (hr : r.Prime) (hdvd : r ∣ 10) :
    r ≤ 5 := by
  have hmem : r ∈ Nat.divisors 10 := by
    rw [Nat.mem_divisors]
    exact ⟨hdvd, by decide⟩
  have hdivs : Nat.divisors 10 = {1, 2, 5, 10} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · exact ((by decide : ¬ Nat.Prime 10) hr).elim

-- End-to-end: replace `5` by `3` in a covering using divisors of `10` that are `≥ 1`.
-- The modulus `1` covers everything on the input side.
example : ∃ res : ℕ → ℤ, Int.IsCoveringSystem
    (((3 ^ (10).factorization 5 * (10 / 5 ^ (10).factorization 5)).divisors.filter
      fun d => 1 ≤ d).image fun d => (res d, d)) := by
  refine MetaMathlibExt.exists_covering_divisors_replace_largest_prime (m := 1)
    (p := 3) (q := 5) (L := 10) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ?_ ?_
  · intro r hr hdvd
    exact prime_dvd_10_le_five r hr hdvd
  · refine ⟨fun _ => 0, ?_⟩
    intro z
    refine ⟨((0 : ℤ), 1), Finset.mem_image_of_mem _ ?_, ?_⟩
    · rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨one_dvd _, by decide⟩, by decide⟩
    · rw [Int.modEq_iff_dvd]
      simp

-- Corollary: a covering using divisors of `10` that are `≥ 2` yields one for the
-- replaced modulus set.
example : (∃ res : ℕ → ℤ, Int.IsCoveringSystem
      (((Nat.divisors 10).filter fun d => 2 ≤ d).image fun d => (res d, d))) →
    ∃ res : ℕ → ℤ, Int.IsCoveringSystem
      (((3 ^ (10).factorization 5 * (10 / 5 ^ (10).factorization 5)).divisors.filter
        fun d => 2 ≤ d).image fun d => (res d, d)) := by
  intro h
  exact MetaMathlibExt.exists_covering_divisors_replace_largest_prime (m := 2)
    (p := 3) (q := 5) (L := 10) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun r hr hdvd => prime_dvd_10_le_five r hr hdvd) h

end MathlibExtTest.NumberTheory.KleinCoveringSystems
