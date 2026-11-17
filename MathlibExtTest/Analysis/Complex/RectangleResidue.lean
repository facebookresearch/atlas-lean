/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.RectangleResidue

/-!
# Tests for the residue theorem on a rectangle (simple poles)
-/

@[expose] public section

open Filter Topology Complex

/-- The square `[-1, 1] × [-1, 1]`, positively oriented. -/
private noncomputable def unitSq : RectilinearRectangle := RectilinearRectangle.ofBounds (-1) 1 (-1) 1

/-- **`∮ ds / s = 2πi`** on the square around `0`. -/
example : unitSq.boundaryIntegral (fun s => 1 / s) = 2 * (Real.pi : ℂ) * I := by
  have h := RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum unitSq {0}
    (fun _ => 1) (fun s => 1 / s) (fun _ => 0)
    (fun p hp => by
      rw [Finset.mem_singleton] at hp
      subst hp
      simp [unitSq])
    (differentiableOn_const _) (fun s _ _ => by simp)
  simpa using h

/-- Two simple poles `±1/2` with residues `1` and `-1`: the boundary integral vanishes. -/
example : unitSq.boundaryIntegral (fun s => 1 / (s - 1 / 2) - 1 / (s + 1 / 2)) = 0 := by
  have h := RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum unitSq {1 / 2, -1 / 2}
    (fun p => if p = 1 / 2 then 1 else -1) (fun s => 1 / (s - 1 / 2) - 1 / (s + 1 / 2))
    (fun _ => 0)
    (fun p hp => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> norm_num [unitSq])
    (differentiableOn_const _) (fun s _ _ => by
      have hne : (1 / 2 : ℂ) ≠ -1 / 2 := by norm_num
      rw [Finset.sum_pair hne]
      norm_num
      ring)
  rw [h]
  have hne : (1 / 2 : ℂ) ≠ -1 / 2 := by norm_num
  rw [Finset.sum_pair hne]
  norm_num

/-- Subtracting the principal part of `1 / s` on the square. -/
example : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g unitSq.carrier ∧
    ∀ s ∈ unitSq.carrier, s ∉ ({0} : Finset ℂ) → 1 / s = g s + ∑ p ∈ ({0} : Finset ℂ), 1 / (s - p) :=
  exists_differentiableOn_eq_add_sum_div_sub unitSq.carrier {0} (fun _ => 1) (fun s => 1 / s)
    (fun p hp => ⟨fun _ => 0, differentiableAt_const _, by
      rw [Finset.mem_singleton] at hp
      subst hp
      exact Eventually.of_forall fun s => by simp⟩)
    (fun s _ hs => by
      have : s ≠ 0 := by simpa using hs
      exact (differentiableAt_const _ |>.div differentiableAt_id this).differentiableWithinAt)

/-- `f'/f = 2 / s` near `0` for `f = s²`. -/
example : ∀ᶠ s in 𝓝[≠] (0 : ℂ), logDeriv (fun s : ℂ => s ^ 2) s =
    ((2 : ℤ) : ℂ) / (s - 0) + logDeriv (fun _ => (1 : ℂ)) s :=
  eventually_logDeriv_eq_of_eq_zpow_mul (k := 2) analyticAt_const one_ne_zero
    (Eventually.of_forall fun s => by simp)

/-- Replacing an analytic numerator by its value at the pole. -/
example : ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ 0 ∧
    ∀ᶠ s in 𝓝[≠] (0 : ℂ), Complex.exp s / s = 1 * Complex.exp 0 / (s - 0) + φ s :=
  exists_eventually_eq_div_sub_add_of_analyticAt (Ψ := fun _ => 0)
    (Complex.differentiable_exp.analyticAt 0) (differentiableAt_const _)
    (Eventually.of_forall fun s => by simp)
