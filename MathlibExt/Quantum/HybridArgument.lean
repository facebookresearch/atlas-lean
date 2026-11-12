/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section



/-- The hybrid argument: if consecutive distributions in a
sequence `p 0, ..., p k` on a finite type are pairwise within
`ε` on the event `E` (in real probability), then the endpoints
are within `k * ε` on `E`. -/
theorem hybrid_argument {α : Type*} [Fintype α]
    (p : ℕ → PMF α) (E : Finset α) {ε : ℝ}
    (hstep : ∀ i, |(∑ a ∈ E, (p i a).toReal) -
      (∑ a ∈ E, (p (i + 1) a).toReal)| ≤ ε) (k : ℕ) :
    |(∑ a ∈ E, (p 0 a).toReal) - (∑ a ∈ E, (p k a).toReal)| ≤ k * ε := by
  induction k with
  | zero => simp
  | succ k ih =>
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
      _ ≤ (k : ℝ) * ε + ε := add_le_add ih (hstep k)
      _ = ((k + 1 : ℕ) : ℝ) * ε := by push_cast; ring

/-- Two-sided consequence for distinguishing advantage between
the first and last hybrid, in the usual form averaged over a
uniform hybrid index is not needed: the same telescoping gives,
for every `j ≤ k`, the bound with `j * ε`. -/
theorem hybrid_argument_le {α : Type*} [Fintype α]
    (p : ℕ → PMF α) (E : Finset α) {ε : ℝ}
    (hstep : ∀ i, |(∑ a ∈ E, (p i a).toReal) -
      (∑ a ∈ E, (p (i + 1) a).toReal)| ≤ ε) {j k : ℕ} (hjk : j ≤ k) :
    |(∑ a ∈ E, (p 0 a).toReal) - (∑ a ∈ E, (p j a).toReal)| ≤ j * ε := by
  have _ := hjk
  exact hybrid_argument p E hstep j

