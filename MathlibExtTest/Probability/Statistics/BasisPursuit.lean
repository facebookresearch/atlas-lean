/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.BasisPursuit

@[expose] public section

open Finset Matrix MathlibExt.Probability.Statistics.LassoRestrictedEigenvalue
  MathlibExt.Probability.Statistics.BasisPursuit

namespace MathlibExtTest.Probability.Statistics.BasisPursuit

/-- An invertible design has the restricted nullspace property over every set. -/
example {n : ℕ} (S : Finset (Fin n)) : RestrictedNullspace (1 : Matrix (Fin n) (Fin n) ℝ) S :=
  fun Δ h _ => by simpa using h

/-- A `3 × 4` design whose nullspace is spanned by `Δ = (1, -1, 1/2, 1/2)`. -/
def X₀ : Matrix (Fin 3) (Fin 4) ℝ := !![1, 1, 0, 0; 0, 0, 1, -1; 1, 0, 0, -2]

/-- The support `S = {0, 1}`. -/
def S₀ : Finset (Fin 4) := {0, 1}

/-- `X₀` fails the restricted nullspace property over `S₀`: `Δ = (1, -1, 1/2, 1/2)` lies in its
nullspace and in the cone `C(S₀; 1)`. -/
lemma not_restrictedNullspace : ¬ RestrictedNullspace X₀ S₀ := by
  intro h
  set Δ : Fin 4 → ℝ := ![1, -1, 1 / 2, 1 / 2] with hΔ
  have hnull : X₀ *ᵥ Δ = 0 := by
    funext i
    fin_cases i <;> simp [X₀, Δ, mulVec, dotProduct, Fin.sum_univ_four]
  have hcone : Δ ∈ cone S₀ 1 := by
    have hc : S₀ᶜ = {2, 3} := by decide
    show ∑ j ∈ S₀ᶜ, |Δ j| ≤ 1 * ∑ j ∈ S₀, |Δ j|
    rw [hc]
    simp [S₀, Δ]
    norm_num
  have h0 := congrFun (h Δ hnull hcone) 0
  simp [Δ] at h0

/-- Yet basis pursuit recovers `θ* = (1, 1, 0, 0)`, supported on `S₀`, as its unique solution:
the restricted nullspace property is necessary for recovering *every* vector supported on `S₀`
(Hastie, Tibshirani and Wainwright, *Statistical Learning with Sparsity*, 2015, Exercise 10.4),
not one fixed vector. This `θ*` is also the unique sparsest solution of `X₀ θ = X₀ θ*`
(`sparsest_fixed`). Read for a fixed `θ*`, the converse in Theorem 10.1 of the same book would
fail here; its Exercise 10.4 states the converse in the uniform form. -/
lemma basisPursuit_unique_fixed :
    ∀ θ : Fin 4 → ℝ, X₀ *ᵥ θ = X₀ *ᵥ ![1, 1, 0, 0] →
      ∑ j, |θ j| ≤ ∑ j, |(![1, 1, 0, 0] : Fin 4 → ℝ) j| → θ = ![1, 1, 0, 0] := by
  intro θ hX hle
  have e0 := congrFun hX 0
  have e1 := congrFun hX 1
  have e2 := congrFun hX 2
  simp [X₀, mulVec, dotProduct, Fin.sum_univ_four] at e0 e1 e2
  simp [Fin.sum_univ_four] at hle
  -- `θ = (1 + 2a, 1 - 2a, a, a)` with `a = θ 3`, and `‖θ‖₁ = |1 + 2a| + |1 - 2a| + 2|a| ≤ 2`.
  have h3 : θ 2 = θ 3 := by linarith
  have h0 : θ 0 = 1 + 2 * θ 3 := by linarith
  have h1 : θ 1 = 1 - 2 * θ 3 := by linarith
  rw [h0, h1, h3] at hle
  have ha : θ 3 = 0 := by
    rcases le_or_gt 0 (θ 3) with ha | ha
    · have : |1 - 2 * θ 3| ≥ 1 - 2 * θ 3 := le_abs_self _
      have : |1 + 2 * θ 3| ≥ 1 + 2 * θ 3 := le_abs_self _
      have : |θ 3| = θ 3 := abs_of_nonneg ha
      linarith
    · have : |1 - 2 * θ 3| ≥ 1 - 2 * θ 3 := le_abs_self _
      have : |1 + 2 * θ 3| ≥ 1 + 2 * θ 3 := le_abs_self _
      have : |θ 3| = -θ 3 := abs_of_neg ha
      linarith
  funext i
  fin_cases i <;> simp [h0, h1, h3, ha]

/-- Every solution of `X₀ θ = X₀ θ*` other than `θ* = (1, 1, 0, 0)` has at least three nonzero
coordinates, so `θ*`, with two, is the unique sparsest solution. -/
lemma sparsest_fixed (θ : Fin 4 → ℝ) (hX : X₀ *ᵥ θ = X₀ *ᵥ ![1, 1, 0, 0])
    (hne : θ ≠ ![1, 1, 0, 0]) :
    3 ≤ (Finset.univ.filter fun j => θ j ≠ 0).card := by
  have e0 := congrFun hX 0
  have e1 := congrFun hX 1
  have e2 := congrFun hX 2
  simp [X₀, mulVec, dotProduct, Fin.sum_univ_four] at e0 e1 e2
  have h3 : θ 2 = θ 3 := by linarith
  have h0 : θ 0 = 1 + 2 * θ 3 := by linarith
  have h1 : θ 1 = 1 - 2 * θ 3 := by linarith
  have ha : θ 3 ≠ 0 := by
    intro ha
    apply hne
    funext i
    fin_cases i <;> simp [h0, h1, h3, ha]
  -- Coordinates `2` and `3` are nonzero, and `θ 0`, `θ 1` cannot both vanish.
  have hsub : ∀ k : Fin 4, k ∈ ({2, 3} : Finset (Fin 4)) →
      k ∈ Finset.univ.filter fun j => θ j ≠ 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp [h3, ha]
  by_cases hz : θ 0 = 0
  · have h1z : θ 1 ≠ 0 := by intro h; linarith
    have : ({1, 2, 3} : Finset (Fin 4)) ⊆ Finset.univ.filter fun j => θ j ≠ 0 := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl <;> simp [h1z, h3, ha]
    simpa using Finset.card_le_card this
  · have : ({0, 2, 3} : Finset (Fin 4)) ⊆ Finset.univ.filter fun j => θ j ≠ 0 := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl <;> simp [hz, h3, ha]
    simpa using Finset.card_le_card this

end MathlibExtTest.Probability.Statistics.BasisPursuit
