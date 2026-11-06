/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import Mathlib.Tactic

/-! Soundness of forward support certificates for an actual signed permutation action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Forward matching on the original support fixes the entire signed-permutation vector. -/
theorem generatedFourth_signed_support_fixed {I : Type*} [Finite I]
    (e : I ≃ I) (σ X Y : I → ℝ) (hσ : ∀ r, σ r ^ 2 = 1)
    (hy : ∀ r, Y (e r) = σ r * X r)
    (hx : ∀ r, X r ≠ 0 → X (e r) = σ r * X r) : Y = X := by
  classical
  let := Fintype.ofFinite I
  have hn : (∑ r, Y r ^ 2) = ∑ r, X r ^ 2 := by
    rw [← Equiv.sum_comp e (fun r => Y r ^ 2)]
    apply Finset.sum_congr rfl
    intro r _
    rw [hy, mul_pow, hσ, one_mul]
  have hc : (∑ r, Y r * X r) = ∑ r, X r ^ 2 := by
    rw [← Equiv.sum_comp e (fun r => Y r * X r)]
    apply Finset.sum_congr rfl
    intro r _
    rw [hy]
    by_cases h : X r = 0
    · simp only [h, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0)]
    · rw [hx r h]
      nlinarith [hσ r]
  have hd : (∑ r, (Y r - X r) ^ 2) = 0 := by
    simp_rw [show ∀ r, (Y r - X r) ^ 2 = Y r ^ 2 + X r ^ 2 - 2 * (Y r * X r) from
      fun r => by ring]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hc, hn]
    ring
  funext r
  have hr := Finset.single_le_sum (fun s _ => sq_nonneg (Y s - X s)) (Finset.mem_univ r)
  rw [hd] at hr
  nlinarith [sq_nonneg (Y r - X r)]

/-- Actual local short-coordinate fixation follows from its full preferred-Q forward phases. -/
theorem generatedFourth_local_short_fixed_of_support (f : localFiberSubgroup)
    (X : GriessShortIndex → ℝ)
    (hx : ∀ r, X r ≠ 0 →
      X (griessShortPermutation f.val.2 r) = qSign (localShortPhase f r) * X r) :
    localShortOperator f X = X := by
  apply generatedFourth_signed_support_fixed (griessShortPermutation f.val.2)
    (fun r => qSign (localShortPhase f r)) X (localShortOperator f X)
  · intro r
    simpa only [pow_two] using qSign_sq (localShortPhase f r)
  · exact localShortOperator_image f X
  · exact hx

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
