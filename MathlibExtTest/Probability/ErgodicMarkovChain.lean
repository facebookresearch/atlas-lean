/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ErgodicMarkovChain

@[expose] public section

open Finset BigOperators
open MathlibExt.Probability.ErgodicMarkovChain

namespace MathlibExtTest.Probability.ErgodicMarkovChain

/-- The uniform chain on two states is ergodic. -/
example : (StochasticMatrix.uniform 1).IsErgodic :=
  StochasticMatrix.isErgodic_uniform 1

/-- The identity chain on two states is not ergodic. -/
example : ¬ (StochasticMatrix.identity 1).IsErgodic :=
  StochasticMatrix.not_isErgodic_identity le_rfl

/-- Every positive power of the uniform chain is ergodic. -/
example {p : ℕ} (hp : 0 < p) : ((StochasticMatrix.uniform 1).pow p).IsErgodic :=
  (StochasticMatrix.isErgodic_uniform 1).pow hp

/-- In an ergodic chain, every pair of states has a positive power with a
positive entry: the uniform chain, one step. -/
example (i j : Fin 2) : ∃ n : ℕ, 0 < n ∧
    0 < (StochasticMatrix.uniform 1).matPow n i j :=
  (StochasticMatrix.isErgodic_uniform 1).exists_matPow_pos i j

/-- Once a power of the uniform chain is all-positive, every later power is:
two steps of the uniform two-state chain are positive everywhere. -/
example (i j : Fin 2) :
    0 < (StochasticMatrix.uniform 1).matPow 2 i j :=
  StochasticMatrix.matPow_pos_of_le_of_pos_pow
    (w := 1)
    (fun i' j' => by rw [StochasticMatrix.matPow_one, StochasticMatrix.prob_uniform]; positivity)
    (by norm_num) i j

/-- Ergodic-level form: past some threshold, every power of the uniform
chain is all-positive. -/
example : ∃ w, 0 < w ∧ ∀ m, w ≤ m → ∀ i j : Fin 2,
    0 < (StochasticMatrix.uniform 1).matPow m i j :=
  (StochasticMatrix.isErgodic_uniform 1).eventually_all_matPow_pos

/-- The two-state chain with an absorbing first state: from state `0` the
chain never leaves, so its `(0, 1)`-entry stays `0` forever. -/
noncomputable def absorbingTwo : StochasticMatrix 1 where
  prob := fun i j =>
    if i = 0 ∧ j = 0 then 1 else if i = 0 ∧ j = 1 then 0 else 1 / 2
  nonneg := fun i j => by
    split_ifs <;> norm_num
  row_sum := fun i => by
    fin_cases i <;> simp

/-- Powers of the absorbing chain never move from state `0` to state `1`. -/
private lemma absorbingTwo_matPow_zero : ∀ n : ℕ,
    absorbingTwo.matPow n 0 1 = 0 := by
  intro n
  induction n with
  | zero => simp [StochasticMatrix.matPow]
  | succ k ih =>
    simp only [StochasticMatrix.matPow]
    have hprob : ∀ k' : Fin 2, absorbingTwo.prob 0 k' * absorbingTwo.matPow k k' 1 =
        if k' = 0 then absorbingTwo.matPow k 0 1 else 0 := by
      intro k'
      fin_cases k' <;> simp [absorbingTwo]
    rw [Finset.sum_congr rfl fun k' _ => hprob k']
    rw [Finset.sum_eq_single 0]
    · simp [ih]
    · intro b _ hb
      simp only [hb, ite_false]
    · intro h0
      exact absurd (Finset.mem_univ (0 : Fin 2)) h0

/-- The absorbing two-state chain is not ergodic, even though state `1`
can reach state `0`: ergodicity needs every pair, in one common power. -/
example : ¬ absorbingTwo.IsErgodic := by
  rintro ⟨n, hn, h⟩
  have h01 := h 0 1
  rw [← StochasticMatrix.matPow_eq_pow, absorbingTwo_matPow_zero] at h01
  exact lt_irrefl 0 h01

/-- Ergodicity of the uniform chain is primitivity of its transition matrix. -/
example : Matrix.IsPrimitive (StochasticMatrix.uniform 1).toMatrix :=
  (StochasticMatrix.isErgodic_iff_isPrimitive _).mp
    (StochasticMatrix.isErgodic_uniform 1)

#print axioms StochasticMatrix.isErgodic_uniform
#print axioms StochasticMatrix.not_isErgodic_identity
#print axioms StochasticMatrix.IsErgodic.pow
#print axioms StochasticMatrix.IsErgodic.eventually_all_matPow_pos

/-- Power zero retains exactly the identity transition probabilities. -/
theorem characterization_power_zero {M : ℕ} (P : StochasticMatrix M)
    (i j : Fin (M + 1)) : P.matPow 0 i j = if i = j then 1 else 0 :=
  rfl

/-- The one-step transition probabilities are the original matrix entries. -/
theorem characterization_power_one {M : ℕ} (P : StochasticMatrix M)
    (i j : Fin (M + 1)) : P.matPow 1 i j = P.prob i j :=
  StochasticMatrix.matPow_one P i j

/-- Three steps of the two-state uniform chain still give literal probability one half. -/
theorem characterization_uniform_three (i j : Fin 2) :
    (StochasticMatrix.uniform 1).matPow 3 i j = (1 / 2 : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [StochasticMatrix.matPow, StochasticMatrix.uniform, Fin.sum_univ_two]

/-- The one-state identity is ergodic, so the nonergodicity guard cannot cover M = 0. -/
theorem characterization_identity_one_state : (StochasticMatrix.identity 0).IsErgodic := by
  refine ⟨1, by norm_num, ?_⟩
  intro i j
  simp only [pow_one]
  fin_cases i
  fin_cases j
  norm_num [StochasticMatrix.toMatrix, StochasticMatrix.identity]

/-- Power zero of an ergodic two-state chain is not ergodic, preserving the positive-p guard. -/
theorem characterization_uniform_power_zero :
    ¬ ((StochasticMatrix.uniform 1).pow 0).IsErgodic := by
  have heq : (StochasticMatrix.uniform 1).pow 0 = StochasticMatrix.identity 1 := by rfl
  rw [heq]
  exact StochasticMatrix.not_isErgodic_identity le_rfl

end MathlibExtTest.Probability.ErgodicMarkovChain
