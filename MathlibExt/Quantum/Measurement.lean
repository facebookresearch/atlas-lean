/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Complex.Basic

/-!
# Projective measurement: Born rule core

If the projected pieces of a vector under a projective
measurement are pairwise orthogonal and sum back to the
vector, the Born-rule probabilities `||P i x||^2` sum to `||x||^2`
(and to `1` for a unit vector). Projectors are left abstract
here; their idempotence and self-adjointness are not
formalized in this module.
-/

@[expose] public section

/-- Projective measurement, Born-rule core of QCI-02: if the
projected pieces `P i x` are pairwise orthogonal and sum back
to `x`, the outcome probabilities `‖P i x‖^2` sum to `‖x‖^2`.
The `P i` are the measurement projectors, left abstract here;
their idempotence and self-adjointness are downstream. -/
theorem measurement_prob_sum {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : ι → E → E) (x : E)
    (hsum : ∑ i, P i x = x)
    (horth : ∀ i j, i ≠ j → inner ℂ (P i x) (P j x) = 0) :
    ∑ i, ‖P i x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hinner : inner ℂ x x = ∑ i, inner ℂ (P i x) (P i x) := by
    have h1 : ∀ i, inner ℂ (P i x) (∑ j, P j x) = inner ℂ (P i x) (P i x) := by
      intro i
      rw [inner_sum]
      apply Finset.sum_eq_single i
      · intro b _ hb
        exact horth i b (Ne.symm hb)
      · intro h
        exact absurd (Finset.mem_univ i) h
    calc inner ℂ x x
        = inner ℂ (∑ i, P i x) (∑ j, P j x) := by conv_lhs => rw [← hsum]
      _ = ∑ i, inner ℂ (P i x) (∑ j, P j x) := by rw [sum_inner]
      _ = ∑ i, inner ℂ (P i x) (P i x) :=
          Finset.sum_congr rfl (fun i _ => h1 i)
  have hcast : ((‖x‖ : ℝ) : ℂ) ^ 2 = ∑ i, (((‖P i x‖ : ℝ) : ℂ) ^ 2) := by
    have h := hinner
    rw [inner_self_eq_norm_sq_to_K] at h
    simp only [inner_self_eq_norm_sq_to_K] at h
    exact h
  have h3 : ((∑ i, ‖P i x‖ ^ 2 : ℝ) : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact hcast.symm
  exact Complex.ofReal_injective h3

/-- For a unit vector the outcome probabilities sum to 1. -/
theorem measurement_prob_sum_one {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : ι → E → E) (x : E) (hx : ‖x‖ = 1)
    (hsum : ∑ i, P i x = x)
    (horth : ∀ i j, i ≠ j → inner ℂ (P i x) (P j x) = 0) :
    ∑ i, ‖P i x‖ ^ 2 = 1 := by
  have h := measurement_prob_sum P x hsum horth
  rw [hx] at h
  simpa using h

end
