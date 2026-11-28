/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Rat.PrescribedSquareClasses

namespace Rat.Place

example (S : Finset Place) (x : (v : S) → (CompletedField v.1)ˣ) :
    ∃ (q : ℚ) (p₀ : Nat.Primes), q ≠ 0 ∧ Place.finite p₀ ∉ S ∧
      (∀ v : S, ∃ y : CompletedField v.1, embedding v.1 q = x v * y ^ 2) ∧
      ∀ p : Nat.Primes, Place.finite p ∉ S → p ≠ p₀ → (Place.finite p).absoluteValue q = 1 :=
  exists_mem_squareClass S x

/- A concrete instance with `S = {∞, 2, 3}`, `x_∞ = -1`, `x_2 = 3` and `x_3 = 2`: some negative
rational number lies in `3 ℚ_2^{×2}` and in `2 ℚ_3^{×2}`, and is a `p`-adic unit at every prime
`p ∉ {2, 3}` except one. -/
example : ∃ (q : ℚ) (p₀ : ℕ), q < 0 ∧ (∃ y : ℚ_[2], (q : ℚ_[2]) = 3 * y ^ 2) ∧
    (∃ y : ℚ_[3], (q : ℚ_[3]) = 2 * y ^ 2) ∧
    ∀ p : Nat.Primes, p.1 ≠ 2 → p.1 ≠ 3 → p.1 ≠ p₀ → (Place.finite p).absoluteValue q = 1 := by
  let c : Place → ℚ
    | .infinite => -1
    | .finite p => if p.1 = 2 then 3 else 2
  have hc : ∀ v, c v ≠ 0 := by
    rintro (_ | p)
    · simp [c]
    · simp only [c]
      split_ifs <;> norm_num
  let two : Nat.Primes := ⟨2, Nat.prime_two⟩
  let three : Nat.Primes := ⟨3, Nat.prime_three⟩
  obtain ⟨q, p₀, hq0, -, hsq, habs⟩ := exists_mem_squareClass
    {.infinite, .finite two, .finite three}
    (fun v => Units.mk0 (embedding v.1 (c v.1)) ((map_ne_zero _).2 (hc v.1)))
  refine ⟨q, p₀.1, ?_, ?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hsq ⟨.infinite, by simp⟩
    change (q : ℝ) = ((-1 : ℚ) : ℝ) * y ^ 2 at hy
    have hle : (q : ℝ) ≤ 0 := by rw [hy]; push_cast; nlinarith [sq_nonneg y]
    exact lt_of_le_of_ne (by exact_mod_cast hle) hq0
  · obtain ⟨y, hy⟩ := hsq ⟨.finite two, by simp⟩
    exact ⟨y, by simpa [c, two, embedding] using hy⟩
  · obtain ⟨y, hy⟩ := hsq ⟨.finite three, by simp⟩
    exact ⟨y, by simpa [c, three, embedding] using hy⟩
  · intro p h2 h3 h₀
    refine habs p ?_ fun h => h₀ (by rw [h])
    simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or, not_or]
    exact ⟨fun h => h2 (by cases h; rfl), fun h => h3 (by cases h; rfl)⟩

end Rat.Place
