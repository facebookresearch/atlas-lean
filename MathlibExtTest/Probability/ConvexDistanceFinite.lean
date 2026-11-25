/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConvexDistanceFinite

/-!
# Tests for the convex-distance inequality on finite product spaces

The uniform weights on `Bool` form a probability vector, so the inequality applies to the fair
coin on `{0, 1}^N`; the convex distance vanishes on `A` and is bounded by the square root of the
Hamming distance.
-/

@[expose] public section

namespace MathlibExtTest.Probability.ConvexDistanceFinite

open MathlibExt.Probability.ConvexDistance

/-- The fair coin. -/
noncomputable def coin : Bool → ℝ := fun _ => 1 / 2

theorem coin_nonneg : ∀ b, 0 ≤ coin b := fun _ => by norm_num [coin]

theorem coin_sum : ∑ b, coin b = 1 := by norm_num [coin]

/-- The set of words starting with `true`. -/
def startsTrue (N : ℕ) : Set (Fin (N + 1) → Bool) := {x | x 0 = true}

/-- The convex-distance inequality for the fair coin and the set of words starting with
`true`. -/
example (N : ℕ) :
    (∑ x, prodWeight coin x * Real.exp (convexDistance (startsTrue N) x ^ 2 / 4)) *
      weightOf coin (startsTrue N) ≤ 1 :=
  sum_exp_convexDistance_mul_weightOf_le coin coin_nonneg coin_sum (N + 1) _

/-- The tail form for the same set at `t = 2`. -/
example (N : ℕ) :
    weightOf coin {x | 2 ≤ convexDistance (startsTrue N) x} * weightOf coin (startsTrue N) ≤
      Real.exp (-2 ^ 2 / 4) :=
  weightOf_le_convexDistance_mul_weightOf_le coin coin_nonneg coin_sum (N + 1) _ (by norm_num)

/-- The section and projection of `startsTrue` at the first coordinate. -/
example (N : ℕ) : sectionAt (startsTrue N) true = Set.univ := by
  ext x; simp [sectionAt, startsTrue]

example (N : ℕ) : sectionAt (startsTrue N) false = ∅ := by
  ext x; simp [sectionAt, startsTrue]

/-- A word outside `startsTrue` is at convex distance at most `1` from it. -/
example (N : ℕ) (x : Fin (N + 1) → Bool) :
    convexDistance (startsTrue N) x ≤ 1 := by
  classical
  have hy : Function.update x 0 true ∈ startsTrue N := by simp [startsTrue]
  refine (convexDistance_le_sqrt_card hy).trans ?_
  rw [Real.sqrt_le_one]
  have : (Finset.univ.filter fun i => x i ≠ Function.update x 0 true i) ⊆ {0} := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra h0
    rw [Finset.mem_singleton] at h0
    exact hi (by rw [Function.update_of_ne h0])
  exact_mod_cast (Finset.card_le_card this).trans (by simp)

/-- The measure form, here for the Dirac mass at `true` on `Bool` (the fair coin is covered by the
sum form above). -/
example (N : ℕ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (convexDistance (startsTrue N) x ^ 2 / 4))
        ∂MeasureTheory.Measure.pi (fun _ => MeasureTheory.Measure.dirac true) ≤
      (MeasureTheory.Measure.pi (fun _ => MeasureTheory.Measure.dirac true)
        (startsTrue N))⁻¹ :=
  lintegral_exp_convexDistance_sq_le_of_fintype _ (N + 1) _

end MathlibExtTest.Probability.ConvexDistanceFinite
