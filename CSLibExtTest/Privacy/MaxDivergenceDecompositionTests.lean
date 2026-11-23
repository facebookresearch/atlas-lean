/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.MaxDivergenceDecomposition

/-!
# Tests for approximate max-divergence decomposition, part 1

Finite Bool regression: `P = (3/4, 1/4)`, `Q = (1/2, 1/2)`, `eps = 0`,
`delta = 1/4`. The naive normalized cap `(2/3, 1/3)` violates the pure
bound while the repaired construction succeeds. Also covers `delta = 0`
and `P = Q` cases.
-/

@[expose] public section

namespace CSLibExtTest.Privacy.MaxDivergenceDecompositionTests

open CSLibExt.Privacy.MaxDivergenceDecomposition
open MathlibExt.Probability.MarkovChainContraction

/-- `P = (3/4, 1/4)` on `Bool` (`false` first). -/
noncomputable def P0 : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal (1 / 4) else ENNReal.ofReal (3 / 4)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- `Q = (1/2, 1/2)` on `Bool`. -/
noncomputable def Q0 : PMF Bool :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1 / 2)) (by
    rw [Fintype.sum_bool]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- Naive normalized cap `(2/3, 1/3)`. -/
noncomputable def Pnaive : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal (1 / 3) else ENNReal.ofReal (2 / 3)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

@[simp]
theorem P0_false_toReal : (P0 false).toReal = 3 / 4 := by
  simp only [P0, PMF.ofFintype_apply, Bool.false_eq_true, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem P0_true_toReal : (P0 true).toReal = 1 / 4 := by
  simp only [P0, PMF.ofFintype_apply, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Q0_false_toReal : (Q0 false).toReal = 1 / 2 := by
  simp only [Q0, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Q0_true_toReal : (Q0 true).toReal = 1 / 2 := by
  simp only [Q0, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Pnaive_false_toReal : (Pnaive false).toReal = 2 / 3 := by
  simp only [Pnaive, PMF.ofFintype_apply, Bool.false_eq_true, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Pnaive_true_toReal : (Pnaive true).toReal = 1 / 3 := by
  simp only [Pnaive, PMF.ofFintype_apply, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

/-- The approximate hypothesis holds for the regression numbers. -/
theorem approx_holds : approxMaxDivLE P0 Q0 0 (1 / 4) := by
  intro s
  simp only [Real.exp_zero, one_mul]
  fin_cases s <;> simp <;> norm_num

/-- The naive normalized cap violates the pure bound. -/
theorem naive_violates : ¬ maxDivLE Pnaive Q0 0 := by
  intro h
  have hf := h false
  simp only [Pnaive_false_toReal, Q0_false_toReal, Real.exp_zero, one_mul] at hf
  norm_num at hf

/-- The repaired construction yields a valid witness. -/
theorem repaired_exists :
    ∃ Ptilde, tvDist P0 Ptilde ≤ 1 / 4 ∧ maxDivLE Ptilde Q0 0 :=
  exists_repair_of_approx P0 Q0 0 (1 / 4) (by norm_num) (by norm_num) approx_holds

/-- Explicit witness: `Q0` itself works for the regression numbers. -/
theorem tvDist_P0_Q0 : tvDist P0 Q0 = 1 / 4 := by
  show (1 / 2) * ∑ w, |(P0 w).toReal - (Q0 w).toReal| = 1 / 4
  simp only [Fintype.sum_bool, P0_false_toReal, P0_true_toReal,
    Q0_false_toReal, Q0_true_toReal]
  norm_num

theorem maxDiv_Q0_self : maxDivLE Q0 Q0 0 := by
  intro w
  cases w <;> simp [Real.exp_zero]

theorem explicit_witness :
    tvDist P0 Q0 ≤ 1 / 4 ∧ maxDivLE Q0 Q0 0 := by
  rw [tvDist_P0_Q0]
  exact ⟨le_refl _, maxDiv_Q0_self⟩

/-- Equal distributions satisfy the approximate bound with zero delta. -/
theorem approx_self_of_nonneg {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps) :
    approxMaxDivLE P P eps 0 := by
  intro s
  have hnonneg : 0 ≤ ∑ w ∈ s, (P w).toReal := by
    apply Finset.sum_nonneg
    intro w _
    exact ENNReal.toReal_nonneg
  have hc : (1 : ℝ) ≤ Real.exp eps := Real.one_le_exp heps
  have hle : (∑ w ∈ s, (P w).toReal) ≤
      Real.exp eps * ∑ w ∈ s, (P w).toReal :=
    le_mul_of_one_le_left hnonneg hc
  linarith

/-- Equal distributions satisfy the pure bound. -/
theorem maxDiv_self_of_nonneg {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P : PMF Outcome) (eps : ℝ) (heps : 0 ≤ eps) :
    maxDivLE P P eps := by
  intro w
  exact le_mul_of_one_le_left ENNReal.toReal_nonneg (Real.one_le_exp heps)

/-- Self distance is a zero-delta witness. -/
theorem self_witness_zero {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P : PMF Outcome) :
    tvDist P P ≤ 0 := by
  have h0 : tvDist P P = 0 :=
    MathlibExt.Probability.MarkovMixing.tvDist_self _
  rw [h0]

#print axioms CSLibExt.Privacy.MaxDivergenceDecomposition.exists_repair_of_approx
#print axioms CSLibExt.Privacy.MaxDivergenceDecomposition.approx_of_exists_repair

end CSLibExtTest.Privacy.MaxDivergenceDecompositionTests
