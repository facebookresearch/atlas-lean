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

/-- The prime divisors of `80` are at most `5`. -/
private theorem prime_dvd_80_le_five (r : ℕ) (hr : r.Prime) (hdvd : r ∣ 80) :
    r ≤ 5 := by
  rw [show (80 : ℕ) = 2 ^ 4 * 5 by decide] at hdvd
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
  · have h2 := Nat.le_of_dvd (by decide) (hr.dvd_of_dvd_pow h)
    omega
  · exact Nat.le_of_dvd (by decide) h

/-- Residues for the divisors of `80` that are at least `2`: the classes `0, 1, 3, 7` modulo
`2, 4, 8, 16` miss exactly `15, 31, 47, 63, 79` modulo `80`, which go to the moduli
`5, 10, 20, 40, 80`. -/
private def res80 : ℕ → ℕ
  | 2 => 0
  | 4 => 1
  | 8 => 3
  | 16 => 7
  | 5 => 15
  | 10 => 31
  | 20 => 47
  | 40 => 63
  | _ => 79

/-- The divisors of `80` that are at least `2` cover the integers; no class has modulus `1`. -/
private theorem cover80 : Int.IsCoveringSystem
    (((Nat.divisors 80).filter fun d => 2 ≤ d).image fun d => ((res80 d : ℤ), d)) := by
  have hfin : ∀ r < 80, ∃ d ∈ [2, 4, 8, 16, 5, 10, 20, 40, 80],
      d ∣ 80 ∧ 2 ≤ d ∧ r % d = res80 d % d := by decide
  intro z
  have h0 : (0 : ℤ) ≤ z % 80 := Int.emod_nonneg z (by decide)
  have hlt : z % 80 < 80 := Int.emod_lt_of_pos z (by decide)
  obtain ⟨d, -, hdvd, h2, hmod⟩ := hfin (z % 80).toNat (by omega)
  refine ⟨((res80 d : ℤ), d), Finset.mem_image_of_mem _ ?_, ?_⟩
  · rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdvd, by decide⟩, h2⟩
  · change z % (d : ℤ) = (res80 d : ℤ) % (d : ℤ)
    rw [← Int.emod_emod_of_dvd z (show (d : ℤ) ∣ 80 by exact_mod_cast hdvd),
      ← Int.toNat_of_nonneg h0]
    exact_mod_cast hmod

/-- The exponent of `5` in `80` is `1`. -/
private theorem factorization_80_five : (80 : ℕ).factorization 5 = 1 := by
  rw [show (80 : ℕ) = 5 * 16 by decide, Nat.factorization_mul (by decide) (by decide),
    Finsupp.add_apply, Nat.Prime.factorization_self (by decide),
    Nat.factorization_eq_zero_of_not_dvd (by decide)]

-- End-to-end on a genuine covering that needs the replaced prime: the divisors of `80`
-- that are at least `2` cover the integers, so replacing `5` by `3` gives a covering by the
-- divisors of `48` that are at least `2`.
example : ∃ res : ℕ → ℤ, Int.IsCoveringSystem
    (((Nat.divisors 48).filter fun d => 2 ≤ d).image fun d => (res d, d)) := by
  have h := MetaMathlibExt.exists_covering_divisors_replace_largest_prime (m := 2)
    (p := 3) (q := 5) (L := 80) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun r hr hdvd => prime_dvd_80_le_five r hr hdvd)
    ⟨fun d => (res80 d : ℤ), cover80⟩
  rw [factorization_80_five, show 3 ^ 1 * (80 / 5 ^ 1) = 48 by decide] at h
  exact h

end MathlibExtTest.NumberTheory.KleinCoveringSystems
