/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.NoRegretDynamics

open MathlibExt.GameTheory.NoRegretDynamics

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- Repeating a pure Nash equilibrium for `T ≥ 1` rounds has no regret, so its empirical
distribution is an exact (`ε = 0`) coarse correlated equilibrium. -/
example (cost : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i)
    (hs : ∀ i a, cost i s ≤ cost i (Function.update s i a)) {T : ℕ} (hT : 0 < T) :
    IsCoarseCorrelatedEq cost (empirical fun _ : Fin T => s) 0 := by
  refine isCoarseCorrelatedEq_empirical hT fun i a => ?_
  simp only [regret, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_zero]
  nlinarith [hs i a, (Nat.cast_nonneg T : (0 : ℝ) ≤ T)]

/-- The empirical distribution of a constant play puts all its mass on that profile. -/
example (s : ∀ i, S i) {T : ℕ} (hT : 0 < T) :
    empirical (fun _ : Fin T => s) s = 1 := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  simp [empirical, hT']

/-- With constant costs, a game is `(1, 0)`-smooth and the extension theorem gives back the
cost itself. -/
example (c : ι → ℝ) {σ : (∀ i, S i) → ℝ} (hσ : IsCoarseCorrelatedEq (fun i _ => c i) σ 0)
    (t : ∀ i, S i) :
    ∑ s, σ s * socialCost (fun i _ => c i) s ≤ socialCost (fun i _ => c i) t := by
  have hsm : IsSmooth (fun i (_ : ∀ i, S i) => c i) 1 0 := fun s t => by
    simp [socialCost]
  simpa using hsm.expected_socialCost_le hσ t

#print axioms isCoarseCorrelatedEq_empirical
#print axioms IsSmooth.expected_socialCost_le
#print axioms IsSmooth.average_socialCost_le
