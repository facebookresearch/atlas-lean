/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainTimeReversal
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

open Matrix ProbabilityTheory

namespace MathlibExtTest.Probability.MarkovChainTimeReversal

/-- Reversed entries for the reversible two-state chain
`P = [[1/2, 1/2], [1/4, 3/4]]`, `π = (1/3, 2/3)`: `P* 0 1 = π 1 * P 1 0 / π 0
= (2/3 * 1/4) / (1/3) = 1/2 = P 0 1`. -/
example :
    (![![1 / 2, 1 / 2], ![1 / 4, 3 / 4]] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
      ![1 / 3, 2 / 3] 1 * (![![1 / 2, 1 / 2], ![1 / 4, 3 / 4]] : Matrix (Fin 2) (Fin 2) ℝ) 1 0 /
        ![1 / 3, 2 / 3] 0 := by
  norm_num

/-- Guard: without stationarity the reversed formula need not be stochastic.
For `P = [[1, 0], [1, 0]]` and `π = (1/2, 1/2)` (not stationary), the reversed
row `0` sums to `2` and row `1` sums to `0`. -/
example :
    (∑ j, ![1 / 2, 1 / 2] j * (![![1, 0], ![1, 0]] : Matrix (Fin 2) (Fin 2) ℝ) j 0 /
        ![1 / 2, 1 / 2] 0) = 2 ∧
      (∑ j, ![1 / 2, 1 / 2] j * (![![1, 0], ![1, 0]] : Matrix (Fin 2) (Fin 2) ℝ) j 1 /
        ![1 / 2, 1 / 2] 1) = 0 := by
  constructor <;> norm_num [Fin.sum_univ_two]

/-! ### Focused applications of the public time-reversal theorems -/

/-- The reversible two-state transition matrix used above. -/
noncomputable def P2 : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1 / 2, 1 / 2], ![1 / 4, 3 / 4]]

/-- Its stationary distribution. -/
noncomputable def pi2 : Fin 2 → ℝ := ![1 / 3, 2 / 3]

theorem P2_rowStochastic : P2 ∈ rowStochastic ℝ (Fin 2) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num [P2]
  · fin_cases i <;> norm_num [P2, Fin.sum_univ_two]

theorem pi2_pos_sum : (∀ i, 0 < pi2 i) ∧ ∑ i, pi2 i = 1 := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [pi2]
  · norm_num [pi2, Fin.sum_univ_two]

theorem pi2_stationary : pi2 ᵥ* P2 = pi2 := by
  funext j
  fin_cases j <;> norm_num [pi2, P2, vecMul, dotProduct, Fin.sum_univ_two]

theorem pi2_detailedBalance : ∀ i j, pi2 i * P2 i j = pi2 j * P2 j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [pi2, P2]

/-- The full-support theorem identifies the reversed matrix with `P2` from
detailed balance. -/
example : Matrix.of (fun i j => pi2 j * P2 j i / pi2 i) = P2 :=
  (timeReversal_of_vecMul_eq_self_of_pos P2_rowStochastic pi2_pos_sum
    pi2_stationary).2.mpr pi2_detailedBalance

/-- The matrix detailed-balance glue theorem, applied in the forward
direction. -/
example : IsDetailedBalance pi2 P2 :=
  (timeReversal_eq_self_iff_isDetailedBalance P2_rowStochastic pi2_pos_sum
    pi2_stationary).mp
    ((timeReversal_of_vecMul_eq_self_of_pos P2_rowStochastic pi2_pos_sum
      pi2_stationary).2.mpr pi2_detailedBalance)

/-- The same two-state chain in the `StochasticMatrix` API. -/
noncomputable def PSM : StochasticMatrix 1 where
  prob := fun i j => P2 i j
  nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [P2]
  row_sum := by
    intro i
    fin_cases i <;> rw [Fin.sum_univ_two] <;> norm_num [P2]

/-- The same stationary distribution in the `StochasticMatrix` API. -/
noncomputable def piSM : StochasticMatrix.Distribution 1 where
  val := pi2
  nonneg := fun i => le_of_lt (pi2_pos_sum.1 i)
  sum_one := pi2_pos_sum.2

theorem PSM_stationary : PSM.IsStationary piSM := by
  intro j
  fin_cases j <;> rw [Fin.sum_univ_two] <;> norm_num [PSM, piSM, pi2, P2]

theorem PSM_detailedBalance : PSM.DetailedBalance piSM := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [PSM, piSM, pi2, P2]

theorem piSM_pos : ∀ i, 0 < piSM.val i := by
  intro i
  fin_cases i <;> norm_num [piSM, pi2]

/-- The `StochasticMatrix` glue theorem produces the same reversal identity. -/
example :
    Matrix.of (fun i j => piSM.val j * PSM.prob j i / piSM.val i) =
      Matrix.of PSM.prob :=
  (PSM.timeReversal_eq_iff_detailedBalance piSM PSM_stationary piSM_pos).mpr
    PSM_detailedBalance

/-- A distribution on three states whose third state has zero mass. -/
noncomputable def pi0 : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]

/-- The reversal of the identity chain on the support of `pi0`, with an
arbitrary uniform stochastic row at the zero-mass state. -/
noncomputable def Pstar0 : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, 0, 0], ![0, 1, 0], ![1 / 3, 1 / 3, 1 / 3]]

theorem pi0_prob : (∀ i, 0 ≤ pi0 i) ∧ ∑ i, pi0 i = 1 := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [pi0]
  · norm_num [pi0, Fin.sum_univ_three]

/-- The general-support theorem handles the zero-mass state and its arbitrary
off-support row: `Pstar0` is row-stochastic and closed on the support of
`pi0`. -/
example :
    Pstar0 ∈ rowStochastic ℝ (Fin 3) ∧
      (∀ i j, pi0 i ≠ 0 → Pstar0 i j ≠ 0 → pi0 j ≠ 0) := by
  have hsupp : ∀ i j, pi0 i ≠ 0 →
      Pstar0 i j = pi0 j * (1 : Matrix (Fin 3) (Fin 3) ℝ) j i / pi0 i := by
    intro i j hi
    fin_cases i
    · fin_cases j <;> norm_num [pi0, Pstar0, Matrix.one_apply]
    · fin_cases j <;> norm_num [pi0, Pstar0, Matrix.one_apply]
    · norm_num [pi0] at hi
  have hoff : ∀ i, pi0 i = 0 →
      (∀ j, 0 ≤ Pstar0 i j) ∧ ∑ j, Pstar0 i j = 1 := by
    intro i hi
    fin_cases i
    · norm_num [pi0] at hi
    · norm_num [pi0] at hi
    · refine ⟨fun j => ?_, ?_⟩
      · fin_cases j <;> norm_num [Pstar0]
      · norm_num [Pstar0, Fin.sum_univ_three]
  obtain ⟨hstoch, hclosed, -⟩ := timeReversal_of_vecMul_eq_self
    (one_mem (Matrix.rowStochastic ℝ (Fin 3))) pi0_prob
    (Matrix.vecMul_one pi0) hsupp hoff
  exact ⟨hstoch, hclosed⟩

end MathlibExtTest.Probability.MarkovChainTimeReversal
