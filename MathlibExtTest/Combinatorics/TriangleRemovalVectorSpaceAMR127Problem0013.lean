/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.TriangleRemovalVectorSpaceAMR127Problem0013

namespace MathlibExt.Combinatorics.TriangleRemovalVectorSpaceAMR127Problem0013Wanted.Tests

open Finset

-- The empty set is triangle-free and has no triangles.
example (n : ℕ) : IsTriangleFree (∅ : Finset (Fin n → ZMod 2)) := by
  simp [IsTriangleFree]

example (n : ℕ) : triangleCount (∅ : Finset (Fin n → ZMod 2)) = 0 := by
  simp [triangleCount]

-- Degenerate triangles count: a set containing `0` is never triangle-free (`0 + 0 = 0`).
example (n : ℕ) (A : Finset (Fin n → ZMod 2)) (h : 0 ∈ A) : ¬ IsTriangleFree A :=
  fun hA => hA 0 h 0 h (by simpa using h)

-- In `𝔽₂¹` every ordered pair of points is a triangle of the whole space.
example : triangleCount (univ : Finset (Fin 1 → ZMod 2)) = 4 := by
  decide

/-- A triangle-free set is disjoint from its translate by any of its elements, so it has at most
half of the points of `𝔽₂ⁿ`. -/
private theorem two_mul_card_le_of_isTriangleFree {n : ℕ} (B : Finset (Fin n → ZMod 2))
    (hB : IsTriangleFree B) : 2 * B.card ≤ 2 ^ n := by
  rcases B.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
  · simp
  have hdisj : Disjoint B (B.image (· + b)) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx'
    exact hB y hy b hb hx
  have hcard : (B.image (· + b)).card = B.card :=
    card_image_of_injective _ (add_left_injective b)
  have h := card_le_univ (B ∪ B.image (· + b))
  rw [card_union_of_disjoint hdisj, hcard] at h
  simpa [two_mul, Fintype.card_fun, ZMod.card] using h

-- The whole space `𝔽₂ⁿ` must lose half of its points to become triangle-free, so the theorem
-- applies to it with `ε = 1/2` (the hypothesis of the theorem is not vacuous).
example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
    c * (1 / 2) ^ C * 4 ^ n ≤ (triangleCount (univ : Finset (Fin n → ZMod 2)) : ℝ) := by
  obtain ⟨c, C, hc, hC, h⟩ := polynomialTriangleRemoval_holds
  refine ⟨c, C, hc, hC, fun n => h n univ (1 / 2) (by norm_num) (by norm_num) ?_⟩
  intro B _ hB
  have h2 := two_mul_card_le_of_isTriangleFree B hB
  have hsd : (univ \ B).card = 2 ^ n - B.card := by
    rw [card_sdiff_of_subset (subset_univ B), card_univ, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
  rw [hsd, Nat.cast_sub (by omega)]
  have h2' : 2 * (B.card : ℝ) ≤ 2 ^ n := by exact_mod_cast h2
  push_cast
  linarith

-- The probabilistic form: `Pr_{x,y}[x, y, x + y ∈ A] ≥ c ε^C` for independent uniform `x, y`.
example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (A : Finset (Fin n → ZMod 2)) (ε : ℝ),
    0 < ε → ε ≤ 1 → (∀ B ⊆ A, IsTriangleFree B → ε * 2 ^ n ≤ ((A \ B).card : ℝ)) →
      c * ε ^ C ≤ (triangleCount A : ℝ) / 4 ^ n := by
  obtain ⟨c, C, hc, hC, h⟩ := polynomialTriangleRemoval_holds
  refine ⟨c, C, hc, hC, fun n A ε h0 h1 hA => ?_⟩
  rw [le_div_iff₀ (by positivity)]
  exact h n A ε h0 h1 hA

end MathlibExt.Combinatorics.TriangleRemovalVectorSpaceAMR127Problem0013Wanted.Tests
