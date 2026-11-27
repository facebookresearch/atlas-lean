/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NotCoveringOfNonintersecting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.NotCoveringOfNonintersecting` -/

namespace MathlibExtTest.NotCoveringOfNonintersecting

open MathlibExt.NumberTheory.ErdosGrahamCoveringWanted

/-- A private test helper: residues for a covering system of divisor form
for `n = 12`. The classes are `0 (mod 2)`, `1 (mod 3)`, `3 (mod 4)`,
`5 (mod 6)` and `9 (mod 12)`. -/
private def coveringResidues12 : ℕ → ℤ := fun d =>
  if d = 3 then 1 else if d = 4 then 3 else if d = 6 then 5
    else if d = 12 then 9 else 0

-- Test section: `n = 2` admits a congruence set of divisor form whose
-- distinct classes overlap only at coprime moduli, vacuously, since `2`
-- is its only divisor greater than `1`. Hence no such covering system
-- exists for `n = 2`.
example : ¬ ∃ b : ℕ → ℤ, Int.IsCoveringSystem
    (((2 : ℕ).divisors.filter (fun d => 1 < d)).image (fun d => (b d, d))) := by
  apply not_covering_of_nonintersecting 2
  refine ⟨fun _ => 0, fun d d' hd hd' h1 h1' hne _ => ?_⟩
  have hd2 : d = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h <;> omega
  have hd'2 : d' = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd' with h | h <;> omega
  exact (hne (by omega)).elim

-- Test section: `n = 6` admits a congruence set of divisor form whose
-- distinct classes overlap only at coprime moduli, with residues
-- `0 (mod 2)`, `0 (mod 3)` and `1 (mod 6)`. The reciprocal sum over the
-- divisors is exactly `1`, so the reciprocal-sum estimate alone does not
-- rule out a covering system here.
example : ¬ ∃ b : ℕ → ℤ, Int.IsCoveringSystem
    (((6 : ℕ).divisors.filter (fun d => 1 < d)).image (fun d => (b d, d))) := by
  apply not_covering_of_nonintersecting 6
  refine ⟨fun d => if d = 6 then 1 else 0, fun d d' hd hd' h1 h1' hne hov => ?_⟩
  obtain ⟨x, hx, hx'⟩ := hov
  have hcomp : (if d = 6 then (1 : ℤ) else 0) ≡ (if d' = 6 then (1 : ℤ) else 0)
      [ZMOD (Nat.gcd d d' : ℤ)] :=
    (hx.of_dvd (show ((Nat.gcd d d' : ℕ) : ℤ) ∣ (d : ℤ) from
      by exact_mod_cast Nat.gcd_dvd_left d d')).symm.trans
      (hx'.of_dvd (show ((Nat.gcd d d' : ℕ) : ℤ) ∣ (d' : ℤ) from
        by exact_mod_cast Nat.gcd_dvd_right d d'))
  have hd3 : d = 2 ∨ d = 3 ∨ d = 6 := by
    have hmem : d ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    have hdiv6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [hdiv6] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hd'3 : d' = 2 ∨ d' = 3 ∨ d' = 6 := by
    have hmem : d' ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hd', by norm_num⟩
    have hdiv6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [hdiv6] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  rcases hd3 with rfl | rfl | rfl <;> rcases hd'3 with rfl | rfl | rfl <;>
    first
      | decide
      | exact absurd hcomp (by decide)
      | exact (hne rfl).elim

-- Test section: the result is sharp at `n = 12`, which does admit a
-- covering system of divisor form. Hence `12` admits no congruence set
-- of divisor form whose distinct classes overlap only at coprime moduli.
example : ¬ ∃ a : ℕ → ℤ,
    ∀ d d' : ℕ, d ∣ 12 → d' ∣ 12 → 1 < d → 1 < d' → d ≠ d' →
      (∃ x : ℤ, x ≡ a d [ZMOD (d : ℤ)] ∧ x ≡ a d' [ZMOD (d' : ℤ)]) →
        Nat.Coprime d d' := by
  rintro ⟨a, ha⟩
  have hcov : Int.IsCoveringSystem
      (((12 : ℕ).divisors.filter (fun d => 1 < d)).image
        (fun d => (coveringResidues12 d, d))) := by
    intro z
    rcases (by omega : z % 12 = 0 ∨ z % 12 = 1 ∨ z % 12 = 2 ∨ z % 12 = 3 ∨
      z % 12 = 4 ∨ z % 12 = 5 ∨ z % 12 = 6 ∨ z % 12 = 7 ∨ z % 12 = 8 ∨
      z % 12 = 9 ∨ z % 12 = 10 ∨ z % 12 = 11) with h | h | h | h | h | h |
      h | h | h | h | h | h
    · exact ⟨(coveringResidues12 2, 2), Finset.mem_image_of_mem _ (by decide),
        by simp [Int.ModEq, coveringResidues12]; omega⟩
    · exact ⟨(coveringResidues12 3, 3), Finset.mem_image_of_mem _ (by decide),
        by simp [Int.ModEq, coveringResidues12]; omega⟩
    · exact ⟨(coveringResidues12 2, 2), Finset.mem_image_of_mem _ (by decide),
        by simp [Int.ModEq, coveringResidues12]; omega⟩
    · exact ⟨(coveringResidues12 4, 4), Finset.mem_image_of_mem _ (by decide),
        by simp [Int.ModEq, coveringResidues12]; omega⟩
    · exact ⟨(coveringResidues12 2, 2), Finset.mem_image_of_mem _ (by decide),
        by simp [Int.ModEq, coveringResidues12]; omega⟩
    · exact ⟨(coveringResidues12 6, 6), Finset.mem_image_of_mem _ (by decide),
        by simp [Int.ModEq, coveringResidues12]; omega⟩
    · exact ⟨(coveringResidues12 2, 2), Finset.mem_image_of_mem _ (by decide),
        by simp [Int.ModEq, coveringResidues12]; omega⟩
    · exact ⟨(coveringResidues12 3, 3), Finset.mem_image_of_mem _ (by decide),
        by simp [Int.ModEq, coveringResidues12]; omega⟩
    · exact ⟨(coveringResidues12 2, 2), Finset.mem_image_of_mem _ (by decide),
        by simp [Int.ModEq, coveringResidues12]; omega⟩
    · exact ⟨(coveringResidues12 12, 12), Finset.mem_image_of_mem _ (by decide),
        by simp [Int.ModEq, coveringResidues12]; omega⟩
    · exact ⟨(coveringResidues12 2, 2), Finset.mem_image_of_mem _ (by decide),
        by simp [Int.ModEq, coveringResidues12]; omega⟩
    · exact ⟨(coveringResidues12 6, 6), Finset.mem_image_of_mem _ (by decide),
        by simp [Int.ModEq, coveringResidues12]; omega⟩
  exact not_covering_of_nonintersecting 12 ⟨a, ha⟩ ⟨coveringResidues12, hcov⟩

end MathlibExtTest.NotCoveringOfNonintersecting
