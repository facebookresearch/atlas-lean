/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Networks.DeGroot
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Topology.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Topology.Order.OrderClosed

/-!
# Boundary tests for DeGroot opinion dynamics

Two-agent examples exercising `tendsto_degrootOpinion`: a primitive matrix whose
consensus is not the arithmetic mean (with weights also derived by
`exists_tendsto_degrootOpinion_consensus`), the empty agent type that rules out that
corollary without `Nonempty`, the periodic swap matrix of Golub-Jackson
Example 1, a non-primitive dictatorial matrix that still reaches consensus, a
dangling node outside the stochastic class with its self-loop repair, and a
doubly-stochastic averaging matrix.

## References

- B. Golub and M. O. Jackson, "Naive Learning in Social Networks and the Wisdom of
  Crowds", American Economic Journal: Microeconomics 2(1) (2010), 112-149. Lemma
  numbers cited here follow the authors' manuscript.
-/

@[expose] public section

namespace MathlibExt.Probability.Networks.DeGrootTest

open scoped Matrix

/-- A primitive influence matrix that is not doubly stochastic. -/
noncomputable def influence : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1/2, 1/2; 1/4, 3/4]

/-- Stationary weights for `influence`. -/
noncomputable def influenceWeights : Fin 2 → ℝ := ![1/3, 2/3]

/-- `influence` is row-stochastic. -/
theorem influence_rowStochastic :
    influence ∈ Matrix.rowStochastic ℝ (Fin 2) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [influence, Matrix.cons_val_zero, Matrix.cons_val_one] ; norm_num
  · intro i
    fin_cases i <;> rw [Fin.sum_univ_two] <;>
      simp [influence, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num

/-- `influence` is primitive: its first power is already entrywise positive. -/
theorem influence_primitive : influence.IsPrimitive := by
  refine ⟨fun i j => Matrix.nonneg_of_mem_rowStochastic influence_rowStochastic,
    1, one_pos, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> rw [pow_one] <;>
    simp [influence, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The weights for `influence` are nonnegative. -/
theorem influenceWeights_nonneg : ∀ j, 0 ≤ influenceWeights j := by
  intro j
  fin_cases j <;>
    simp [influenceWeights, Matrix.cons_val_zero, Matrix.cons_val_one] ;
      norm_num

/-- The weights for `influence` sum to 1. -/
theorem influenceWeights_sum : ∑ j, influenceWeights j = 1 := by
  rw [Fin.sum_univ_two]
  simp [influenceWeights, Matrix.cons_val_zero, Matrix.cons_val_one] ;
    norm_num

/-- The weights for `influence` are stationary. -/
theorem influenceWeights_stationary :
    influenceWeights ᵥ* influence = influenceWeights := by
  funext j
  fin_cases j <;> rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two] <;>
    simp [influenceWeights, influence, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;> norm_num

/-- Agent 0's opinions under `influence` tend to `2 / 3`. -/
theorem influence_tendsto :
    Filter.Tendsto (fun t => degrootOpinion influence ![0, 1] t 0) Filter.atTop
      (nhds (2 / 3)) := by
  have h := tendsto_degrootOpinion influence_rowStochastic influence_primitive
    influenceWeights_nonneg influenceWeights_sum influenceWeights_stationary
    ![0, 1] 0
  have hdot : influenceWeights ⬝ᵥ ![0, 1] = 2 / 3 := by
    change (∑ i, influenceWeights i * (![0, 1] : Fin 2 → ℝ) i) = _
    rw [Fin.sum_univ_two]
    simp [influenceWeights, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hdot] at h
  exact h

/-- Consensus under `influence` is not the arithmetic mean. -/
theorem influence_not_mean : (2 / 3 : ℝ) ≠ (0 + 1) / 2 := by norm_num

/-- Consensus under `influence` in the product topology. -/
theorem influence_consensus :
    Filter.Tendsto (degrootOpinion influence ![0, 1]) Filter.atTop
      (nhds (fun _ => (2 / 3 : ℝ))) := by
  have h := tendsto_degrootOpinion_consensus influence_rowStochastic
    influence_primitive influenceWeights_nonneg influenceWeights_sum
    influenceWeights_stationary ![0, 1]
  have hdot : influenceWeights ⬝ᵥ ![0, 1] = 2 / 3 := by
    change (∑ i, influenceWeights i * (![0, 1] : Fin 2 → ℝ) i) = _
    rw [Fin.sum_univ_two]
    simp [influenceWeights, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hdot] at h
  exact h

/-- Consensus for `influence` from row-stochasticity and primitivity alone: the weights
that `exists_tendsto_degrootOpinion_consensus` derives are `influenceWeights`. -/
theorem influence_derived_weights :
    ∃ π : Fin 2 → ℝ, π = influenceWeights ∧
      ∀ x₀ : Fin 2 → ℝ, Filter.Tendsto (degrootOpinion influence x₀) Filter.atTop
        (nhds (fun _ => π ⬝ᵥ x₀)) := by
  obtain ⟨π, -, hπ1, hstat, hlim⟩ :=
    exists_tendsto_degrootOpinion_consensus influence_rowStochastic influence_primitive
  exact ⟨π, (FiniteMarkovChainConvergence.stationary_unique influence_rowStochastic
    influence_primitive influenceWeights_nonneg influenceWeights_sum
    influenceWeights_stationary hπ1 hstat).symm, hlim⟩

/-- Why `exists_tendsto_degrootOpinion_consensus` needs a nonempty agent type: on
`Fin 0` every matrix is row-stochastic and primitive, yet no weights sum to `1`. -/
theorem empty_agents_no_weights (T : Matrix (Fin 0) (Fin 0) ℝ) :
    T ∈ Matrix.rowStochastic ℝ (Fin 0) ∧ T.IsPrimitive ∧
      ¬ ∃ π : Fin 0 → ℝ, ∑ j, π j = 1 := by
  refine ⟨?_, ⟨fun i => i.elim0, 1, one_pos, fun i => i.elim0⟩, ?_⟩
  · rw [Matrix.mem_rowStochastic_iff_sum]
    exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  · rintro ⟨π, hπ⟩
    simp at hπ

/-- The periodic swap matrix of Golub-Jackson Example 1. -/
def swap : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- `swap` is row-stochastic. -/
theorem swap_rowStochastic : swap ∈ Matrix.rowStochastic ℝ (Fin 2) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [swap, Matrix.cons_val_zero, Matrix.cons_val_one]
  · intro i
    fin_cases i <;> rw [Fin.sum_univ_two] <;>
      simp [swap, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The uniform weights are stationary for `swap`. -/
theorem swap_uniform_stationary :
    (![1 / 2, 1 / 2] : Fin 2 → ℝ) ᵥ* swap = ![1 / 2, 1 / 2] := by
  funext j
  fin_cases j <;> rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two] <;>
    simp [swap, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Opinions under `swap` alternate between the initial vector and its swap. -/
private theorem swap_opinion_aux (t : ℕ) :
    (Even t → degrootOpinion swap ![0, 1] t = ![0, 1]) ∧
    (Odd t → degrootOpinion swap ![0, 1] t = ![1, 0]) := by
  induction t with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro _
        exact degrootOpinion_zero
      · intro h
        have hne : ¬ Odd (0 : ℕ) := by
          intro h'
          obtain ⟨m, hm⟩ := h'
          omega
        exact absurd h hne
  | succ t ih =>
      have hev : Even (t + 1) ↔ Odd t :=
        Nat.even_add_one.trans Nat.not_even_iff_odd
      have hod : Odd (t + 1) ↔ Even t :=
        Nat.odd_add_one.trans Nat.not_odd_iff_even
      refine ⟨?_, ?_⟩
      · intro h
        have ht : Odd t := hev.mp h
        rw [degrootOpinion_succ, ih.2 ht]
        funext i
        fin_cases i <;> rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] <;>
          simp [swap, Matrix.cons_val_zero, Matrix.cons_val_one]
      · intro h
        have ht : Even t := hod.mp h
        rw [degrootOpinion_succ, ih.1 ht]
        funext i
        fin_cases i <;> rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] <;>
          simp [swap, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Under `swap`, agent 0's opinion is `0` at even times. -/
theorem swap_opinion_even (t : ℕ) (ht : Even t) :
    degrootOpinion swap ![0, 1] t 0 = 0 := by
  rw [(swap_opinion_aux t).1 ht]
  simp [Matrix.cons_val_zero]

/-- Under `swap`, agent 0's opinion is `1` at odd times. -/
theorem swap_opinion_odd (t : ℕ) (ht : Odd t) :
    degrootOpinion swap ![0, 1] t 0 = 1 := by
  rw [(swap_opinion_aux t).2 ht]
  simp [Matrix.cons_val_zero]

/-- Under `swap`, agent 0's opinions do not converge to any limit. -/
theorem swap_no_limit (c : ℝ) :
    ¬ Filter.Tendsto (fun t => degrootOpinion swap ![0, 1] t 0) Filter.atTop
      (nhds c) := by
  intro h
  have hmem : Set.Ioo (c - 1 / 4) (c + 1 / 4) ∈ nhds c :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hev : ∀ᶠ t in Filter.atTop,
      degrootOpinion swap ![0, 1] t 0 ∈ Set.Ioo (c - 1 / 4) (c + 1 / 4) :=
    h.eventually hmem
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have h0 := hN (2 * N) (by omega)
  have h1 := hN (2 * N + 1) (by omega)
  rw [swap_opinion_even _ (even_two_mul N)] at h0
  rw [swap_opinion_odd _ ⟨N, rfl⟩] at h1
  simp only [Set.mem_Ioo] at h0 h1
  linarith

/-- `swap` is not primitive, since otherwise opinions would converge. -/
theorem swap_not_primitive : ¬ swap.IsPrimitive := by
  intro hprim
  have h0 : ∀ j : Fin 2, 0 ≤ (![1 / 2, 1 / 2] : Fin 2 → ℝ) j := by
    intro j
    fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : ∑ j : Fin 2, (![1 / 2, 1 / 2] : Fin 2 → ℝ) j = 1 := by
    rw [Fin.sum_univ_two]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] ; norm_num
  have hconv :=
    tendsto_degrootOpinion swap_rowStochastic hprim h0 h1 swap_uniform_stationary
      ![0, 1] 0
  exact swap_no_limit _ hconv

/-- A dictatorial influence matrix: everyone copies agent 0. -/
def dictator : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 0]

/-- `dictator` is row-stochastic. -/
theorem dictator_rowStochastic :
    dictator ∈ Matrix.rowStochastic ℝ (Fin 2) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [dictator, Matrix.cons_val_zero, Matrix.cons_val_one]
  · intro i
    fin_cases i <;> rw [Fin.sum_univ_two] <;>
      simp [dictator, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The weights concentrated on agent 0 are stationary for `dictator`. -/
theorem dictator_weights_stationary :
    (![1, 0] : Fin 2 → ℝ) ᵥ* dictator = ![1, 0] := by
  funext j
  fin_cases j <;> rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two] <;>
    simp [dictator, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Every row of `dictator` selects agent 0's entry. -/
private theorem dictator_mulVec_apply (v : Fin 2 → ℝ) (i : Fin 2) :
    (dictator *ᵥ v) i = v 0 := by
  fin_cases i <;> rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] <;>
    simp [dictator, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- From time `1` on, every agent holds agent 0's initial belief. -/
theorem dictator_collapse (x₀ : Fin 2 → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    degrootOpinion dictator x₀ t = fun _ => x₀ 0 := by
  induction t, ht using Nat.le_induction with
  | base =>
      change degrootOpinion dictator x₀ (0 + 1) = _
      rw [degrootOpinion_succ, degrootOpinion_zero]
      funext i
      exact dictator_mulVec_apply x₀ i
  | succ n hn ih =>
      rw [degrootOpinion_succ, ih]
      funext i
      exact dictator_mulVec_apply _ i

/-- Each agent's opinions tend to agent 0's initial belief. -/
theorem dictator_tendsto (x₀ : Fin 2 → ℝ) (i : Fin 2) :
    Filter.Tendsto (fun t => degrootOpinion dictator x₀ t i) Filter.atTop
      (nhds ((![1, 0] : Fin 2 → ℝ) ⬝ᵥ x₀)) := by
  have heq : (fun t => degrootOpinion dictator x₀ t i) =ᶠ[Filter.atTop]
      (fun _ => x₀ 0) := by
    change ∀ᶠ t in Filter.atTop, degrootOpinion dictator x₀ t i = x₀ 0
    rw [Filter.eventually_atTop]
    exact ⟨1, fun t ht => congrFun (dictator_collapse x₀ t ht) i⟩
  have hlim : Filter.Tendsto (fun t => degrootOpinion dictator x₀ t i)
      Filter.atTop (nhds (x₀ 0)) :=
    Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  have hdot : ((![1, 0] : Fin 2 → ℝ) ⬝ᵥ x₀) = x₀ 0 := by
    change (∑ j, (![1, 0] : Fin 2 → ℝ) j * x₀ j) = _
    rw [Fin.sum_univ_two]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hdot]
  exact hlim

/-- The second column of `dictator` is identically zero. -/
private theorem dictator_col1_zero (j : Fin 2) : dictator j 1 = 0 := by
  fin_cases j <;> simp [dictator, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Every positive power of `dictator` has a zero entry. -/
private theorem dictator_pow_zero_entry (k : ℕ) (hk : 1 ≤ k) :
    (dictator ^ k) 0 1 = 0 := by
  induction k, hk using Nat.le_induction with
  | base =>
      rw [pow_one]
      simp [dictator, Matrix.cons_val_zero, Matrix.cons_val_one]
  | succ n hn ih =>
      rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, dictator_col1_zero,
        dictator_col1_zero, mul_zero, mul_zero, add_zero]

/-- `dictator` is not primitive: primitivity is sufficient, not necessary. -/
theorem dictator_not_primitive : ¬ dictator.IsPrimitive := by
  rintro ⟨_, k, hkpos, hpos⟩
  have hk1 : 1 ≤ k := by omega
  have h0 := dictator_pow_zero_entry k hk1
  have h1 := hpos 0 1
  exact ne_of_gt h1 h0

/-- A dangling node: the second row sums to `0`, so this is not stochastic. -/
noncomputable def dangling : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/2; 0, 0]

/-- The self-loop repair of `dangling`, which is stochastic. -/
noncomputable def danglingSelfLoop : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1/2, 1/2; 0, 1]

/-- `dangling` is not row-stochastic. -/
theorem dangling_not_rowStochastic :
    dangling ∉ Matrix.rowStochastic ℝ (Fin 2) := by
  intro h
  have h1 := Matrix.sum_row_of_mem_rowStochastic h 1
  simp [dangling, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h1

/-- The self-loop repair is row-stochastic. -/
theorem danglingSelfLoop_rowStochastic :
    danglingSelfLoop ∈ Matrix.rowStochastic ℝ (Fin 2) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [danglingSelfLoop, Matrix.cons_val_zero, Matrix.cons_val_one]
  · intro i
    fin_cases i <;> rw [Fin.sum_univ_two] <;>
      simp [danglingSelfLoop, Matrix.cons_val_zero, Matrix.cons_val_one] ;
        norm_num

/-- Every positive power of the repair has a zero entry. -/
private theorem danglingSelfLoop_pow_zero_entry (k : ℕ) (hk : 1 ≤ k) :
    (danglingSelfLoop ^ k) 1 0 = 0 := by
  induction k, hk using Nat.le_induction with
  | base =>
      rw [pow_one]
      simp [danglingSelfLoop, Matrix.cons_val_zero, Matrix.cons_val_one]
  | succ n hn ih =>
      rw [pow_succ', Matrix.mul_apply, Fin.sum_univ_two, ih]
      simp [danglingSelfLoop, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The self-loop repair is not primitive. -/
theorem danglingSelfLoop_not_primitive : ¬ danglingSelfLoop.IsPrimitive := by
  rintro ⟨_, k, hkpos, hpos⟩
  have hk1 : 1 ≤ k := by omega
  have h0 := danglingSelfLoop_pow_zero_entry k hk1
  have h1 := hpos 1 0
  exact ne_of_gt h1 h0

/-- The absorbing agent keeps its initial belief for all time. -/
theorem danglingSelfLoop_absorbing (x₀ : Fin 2 → ℝ) (t : ℕ) :
    degrootOpinion danglingSelfLoop x₀ t 1 = x₀ 1 := by
  induction t with
  | zero =>
      rw [degrootOpinion_zero]
  | succ n ih =>
      rw [degrootOpinion_succ, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two,
        ih]
      simp [danglingSelfLoop, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A doubly-stochastic primitive averaging matrix. -/
noncomputable def averaging : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2/3, 1/3; 1/3, 2/3]

/-- `averaging` is doubly stochastic. -/
theorem averaging_doublyStochastic :
    averaging ∈ doublyStochastic ℝ (Fin 2) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [averaging, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num
  · intro i
    fin_cases i <;> rw [Fin.sum_univ_two] <;>
      simp [averaging, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num
  · intro j
    fin_cases j <;> rw [Fin.sum_univ_two] <;>
      simp [averaging, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num

/-- `averaging` is primitive. -/
theorem averaging_primitive : averaging.IsPrimitive := by
  refine ⟨?_, 1, one_pos, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [averaging, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num
  · intro i j
    fin_cases i <;> fin_cases j <;> rw [pow_one] <;>
      simp [averaging, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Agent 0's opinions tend to the arithmetic mean of the initial beliefs. -/
theorem averaging_tendsto (x₀ : Fin 2 → ℝ) :
    Filter.Tendsto (fun t => degrootOpinion averaging x₀ t 0) Filter.atTop
      (nhds ((x₀ 0 + x₀ 1) / 2)) := by
  have h := tendsto_degrootOpinion_of_mem_doublyStochastic
    averaging_doublyStochastic averaging_primitive x₀ 0
  simpa [Fin.sum_univ_two, Fintype.card_fin] using h

end MathlibExt.Probability.Networks.DeGrootTest
