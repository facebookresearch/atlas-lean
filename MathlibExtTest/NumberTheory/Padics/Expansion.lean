/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Padics.Expansion

set_option autoImplicit false

open PadicInt Finset

namespace PadicIntTest

variable {p : ℕ} [Fact p.Prime]

/-- Uniqueness: equal digits force equal `p`-adic integers. -/
theorem test_eq_of_padicDigit_eq {a a' : ℤ_[p]}
    (h : ∀ n, padicDigit a n = padicDigit a' n) : a = a' :=
  eq_of_padicDigit_eq h

/-- Existence: the zero digit sequence is realized. -/
theorem test_exists_zero_digits :
    ∃ a : ℤ_[p], ∀ n, padicDigit a n = 0 := by
  refine exists_padicDigit_eq (fun _ => 0) (fun _ => ?_)
  exact Nat.Prime.pos (Fact.out : p.Prime)

/-- Existence: the constant digit sequence `p - 1` is realized. -/
theorem test_exists_const_pred_digits :
    ∃ a : ℤ_[p], ∀ n, padicDigit a n = p - 1 := by
  refine exists_padicDigit_eq (fun _ => p - 1) (fun _ => ?_)
  have hp : 0 < p := Nat.Prime.pos (Fact.out : p.Prime)
  omega

/-- Existence + uniqueness: every admissible digit sequence is realized
by a unique `p`-adic integer. -/
theorem test_existsUnique_digits (b : ℕ → ℕ) (hb : ∀ n, b n < p) :
    ∃! a : ℤ_[p], ∀ n, padicDigit a n = b n :=
  existsUnique_padicDigit_eq b hb

/-- Two realizations of the same digit sequence coincide. -/
theorem test_exists_realizations_agree (b : ℕ → ℕ)
    {a₁ a₂ : ℤ_[p]} (h₁ : ∀ n, padicDigit a₁ n = b n)
    (h₂ : ∀ n, padicDigit a₂ n = b n) : a₁ = a₂ :=
  eq_of_padicDigit_eq (fun n => (h₁ n).trans (h₂ n).symm)

/-- Sparse digits: the sequence that is `1` at place `2` and `0` elsewhere
is realized, with the expected digits at places `0`, `1`, `2`, `3`. -/
theorem test_exists_sparse_digits :
    ∃ a : ℤ_[p], padicDigit a 0 = 0 ∧ padicDigit a 1 = 0 ∧
      padicDigit a 2 = 1 ∧ padicDigit a 3 = 0 := by
  have hp : 0 < p := Nat.Prime.pos (Fact.out : p.Prime)
  have hb : ∀ n, (if n = 2 then 1 else 0) < p := by
    intro n
    split_ifs with h
    · exact Nat.Prime.one_lt (Fact.out : p.Prime)
    · exact hp
  obtain ⟨a, ha⟩ := exists_padicDigit_eq (fun n => if n = 2 then 1 else 0) hb
  exact ⟨a, by simpa using ha 0, by simpa using ha 1, by simpa using ha 2,
    by simpa using ha 3⟩

/-- Bundled expansion: the realization of `b` has bundled expansion
`⟨b n, hb n⟩` at every place. -/
theorem test_padicExpansion_of_exists (b : ℕ → ℕ) (hb : ∀ n, b n < p) :
    ∃ a : ℤ_[p], ∀ n, padicExpansion a n = ⟨b n, hb n⟩ := by
  obtain ⟨a, ha⟩ := padicExpansion_surjective (fun n => ⟨b n, hb n⟩)
  exact ⟨a, congrFun ha⟩

/-- Finite reconstruction for a realization of `b`: its `n`-th approximation
is the partial digit sum `∑ k < n, b k * p ^ k`. -/
theorem test_appr_of_exists (b : ℕ → ℕ) (hb : ∀ n, b n < p) :
    ∃ a : ℤ_[p], ∀ n, a.appr n = ∑ k ∈ Finset.range n, b k * p ^ k := by
  obtain ⟨a, ha⟩ := exists_padicDigit_eq b hb
  refine ⟨a, fun n => ?_⟩
  rw [appr_eq_sum_padicDigit]
  exact Finset.sum_congr rfl (fun k _ => by rw [ha k])

end PadicIntTest
