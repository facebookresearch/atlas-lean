/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section



/-- The hybrid argument: if consecutive distributions in a
sequence `p 0, ..., p k` on a finite type are pairwise within
`ε` on the event `E` (in real probability), then the endpoints
are within `k * ε` on `E`. -/
theorem hybrid_argument {α : Type*} [Fintype α]
    (p : ℕ → PMF α) (E : Finset α) {ε : ℝ} (k : ℕ)
    (hstep : ∀ i < k, |(∑ a ∈ E, (p i a).toReal) -
      (∑ a ∈ E, (p (i + 1) a).toReal)| ≤ ε) :
    |(∑ a ∈ E, (p 0 a).toReal) - (∑ a ∈ E, (p k a).toReal)| ≤ k * ε := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih fun i hi => hstep i (Nat.lt_succ_of_lt hi)
    have htri : |(∑ a ∈ E, (p 0 a).toReal) - (∑ a ∈ E, (p (k + 1) a).toReal)| ≤
        |(∑ a ∈ E, (p 0 a).toReal) - (∑ a ∈ E, (p k a).toReal)| +
        |(∑ a ∈ E, (p k a).toReal) - (∑ a ∈ E, (p (k + 1) a).toReal)| := by
      have h : (∑ a ∈ E, (p 0 a).toReal) - (∑ a ∈ E, (p (k + 1) a).toReal) =
          ((∑ a ∈ E, (p 0 a).toReal) - (∑ a ∈ E, (p k a).toReal)) +
          ((∑ a ∈ E, (p k a).toReal) - (∑ a ∈ E, (p (k + 1) a).toReal)) := by
        ring
      rw [h]
      exact abs_add_le _ _
    calc |(∑ a ∈ E, (p 0 a).toReal) - (∑ a ∈ E, (p (k + 1) a).toReal)|
        ≤ |(∑ a ∈ E, (p 0 a).toReal) - (∑ a ∈ E, (p k a).toReal)| +
          |(∑ a ∈ E, (p k a).toReal) - (∑ a ∈ E, (p (k + 1) a).toReal)| := htri
      _ ≤ (k : ℝ) * ε + ε := add_le_add ih (hstep k (Nat.lt_succ_self k))
      _ = ((k + 1 : ℕ) : ℝ) * ε := by push_cast; ring

/-- Prefix form of the hybrid argument: if consecutive distributions in
`p 0, ..., p k` are pairwise within `ε` on `E`, then for every `j ≤ k`
the hybrids `p 0` and `p j` are within `j * ε` on `E`. -/
theorem hybrid_argument_le {α : Type*} [Fintype α]
    (p : ℕ → PMF α) (E : Finset α) {ε : ℝ} {j k : ℕ} (hjk : j ≤ k)
    (hstep : ∀ i < k, |(∑ a ∈ E, (p i a).toReal) -
      (∑ a ∈ E, (p (i + 1) a).toReal)| ≤ ε) :
    |(∑ a ∈ E, (p 0 a).toReal) - (∑ a ∈ E, (p j a).toReal)| ≤ j * ε :=
  hybrid_argument p E j fun i hi => hstep i (lt_of_lt_of_le hi hjk)
