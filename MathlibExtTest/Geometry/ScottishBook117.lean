/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.ScottishBook117
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Tests for `MathlibExt.Geometry.ScottishBook117` -/

namespace MathlibExtTest.ScottishBook117

open MathlibExt.Geometry.ScottishBook117Wanted

/-- The unit vector `(1, 0, 0)`. -/
private noncomputable def e₀ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1

private theorem norm_e₀ : ‖e₀‖ = 1 := by simp [e₀]

private theorem sign_mul_abs (r : ℝ) : Real.sign r * |r| = r := by
  rcases lt_trichotomy r 0 with h | rfl | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    ring
  · simp
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

-- Test section: oriented tangents. A line traversed at unit speed has an oriented tangent at
-- every parameter, in its direction of travel.
example (t : ℝ) : HasTangentLineAt (fun s => s • e₀) t := by
  refine ⟨e₀, norm_e₀, fun ε hε => ⟨1, one_pos, fun s _ _ => ?_⟩⟩
  beta_reduce
  rw [← sub_smul, norm_smul, Real.norm_eq_abs, norm_e₀, mul_one, sign_mul_abs, sub_self,
    norm_zero]
  positivity

-- The folded line `s ↦ |s| • e₀` runs out along the same ray on both sides of `0`. Its secants
-- from the origin all lie on one line, but their directions tend to `e₀` from both sides instead
-- of to opposite vectors, so it has no oriented tangent at `0`.
example : ¬ HasTangentLineAt (fun s => |s| • e₀) 0 := by
  rintro ⟨v, -, h⟩
  obtain ⟨δ, hδ, hs⟩ := h (1 / 2) (by norm_num)
  have ha : 0 < δ / 2 := half_pos hδ
  have key : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → ‖e₀ - σ • v‖ ≤ 1 / 2 := by
    intro σ hσ
    have hσa : |σ * (δ / 2)| = δ / 2 := by
      rcases hσ with rfl | rfl <;> simp [abs_of_pos ha]
    have hsign : Real.sign (σ * (δ / 2)) = σ := by
      rcases hσ with rfl | rfl
      · rw [one_mul, Real.sign_of_pos ha]
      · rw [neg_one_mul, Real.sign_of_neg (neg_neg_of_pos ha)]
    have h1 := hs (σ * (δ / 2)) (by rw [sub_zero, hσa]; exact ha)
      (by rw [sub_zero, hσa]; exact half_lt_self hδ)
    beta_reduce at h1
    rw [sub_zero, hσa, abs_zero, zero_smul, sub_zero, hsign, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha, norm_e₀, mul_one, mul_comm σ, ← smul_smul, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos ha] at h1
    nlinarith
  have h1 := key 1 (Or.inl rfl)
  have h2 := key (-1) (Or.inr rfl)
  rw [one_smul] at h1
  rw [neg_one_smul, sub_neg_eq_add] at h2
  have h3 : ‖(2 : ℝ) • e₀‖ ≤ 1 :=
    calc ‖(2 : ℝ) • e₀‖ = ‖(e₀ - v) + (e₀ + v)‖ := by congr 1; module
      _ ≤ ‖e₀ - v‖ + ‖e₀ + v‖ := norm_add_le _ _
      _ ≤ 1 := by linarith
  rw [norm_smul, norm_e₀] at h3
  norm_num at h3

-- Test section: the theorem. The claim of Problem 117 is false.
example : ¬ ScottishBookProblem117Claim := frechet117_refuted

-- Unfolded: some closed curve with an oriented tangent at every parameter has no
-- reparametrization, with the same image, that is differentiable with nonzero derivative at
-- every parameter.
example : ∃ γ : ℝ → EuclideanSpace ℝ (Fin 3), (∀ t, γ (t + 1) = γ t) ∧ Continuous γ ∧
    Set.InjOn γ (Set.Ico (0 : ℝ) 1) ∧ (∀ t, HasTangentLineAt γ t) ∧
    ∀ p : ℝ → EuclideanSpace ℝ (Fin 3), (∀ t, p (t + 1) = p t) → Continuous p →
      Set.InjOn p (Set.Ico (0 : ℝ) 1) → Set.range p = Set.range γ →
      ∃ t, ¬ DifferentiableAt ℝ p t ∨ deriv p t = 0 := by
  by_contra hne
  apply frechet117_refuted
  intro γ h1 h2 h3 h4
  by_contra hp
  refine hne ⟨γ, h1, h2, h3, h4, fun p hp1 hp2 hp3 hp4 => ?_⟩
  by_contra ht
  refine hp ⟨p, hp1, hp2, hp3, hp4, fun t => ?_⟩
  by_contra h'
  exact ht ⟨t, by tauto⟩

end MathlibExtTest.ScottishBook117
