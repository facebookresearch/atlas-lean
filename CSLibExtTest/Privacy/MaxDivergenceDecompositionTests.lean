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

/-
Part-2 tests for `approxMaxDivLE_both_iff_exists_repair`, with
`eps = Real.log 2` throughout: symmetric case (a), unequal-excess
case (b), and the `delta = 0` boundary (c).
-/

namespace CSLibExtTest.Privacy.MaxDivergenceDecompositionPart2Tests

open CSLibExt.Privacy.MaxDivergenceDecomposition
open MathlibExt.Probability.MarkovChainContraction

/-- `Real.exp (Real.log 2) = 2`. -/
theorem exp_log_two : Real.exp (Real.log 2) = 2 :=
  Real.exp_log (by norm_num)

/-- `Real.log 2` is nonnegative. -/
theorem log_two_nonneg : 0 ≤ Real.log 2 :=
  Real.log_nonneg (by norm_num)

/-- Case (a): `Pa = (4/5, 1/5)` on `Bool` (`false` first). -/
noncomputable def Pa : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal (1 / 5) else ENNReal.ofReal (4 / 5)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- Case (a): `Qa = (1/5, 4/5)` on `Bool`. -/
noncomputable def Qa : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal (4 / 5) else ENNReal.ofReal (1 / 5)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- Case (a) witness: `Pa' = (2/3, 1/3)`. -/
noncomputable def Pa' : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal (1 / 3) else ENNReal.ofReal (2 / 3)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- Case (a) witness: `Qa' = (1/3, 2/3)`. -/
noncomputable def Qa' : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal (2 / 3) else ENNReal.ofReal (1 / 3)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

@[simp]
theorem Pa_false_toReal : (Pa false).toReal = 4 / 5 := by
  simp only [Pa, PMF.ofFintype_apply, Bool.false_eq_true, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Pa_true_toReal : (Pa true).toReal = 1 / 5 := by
  simp only [Pa, PMF.ofFintype_apply, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Qa_false_toReal : (Qa false).toReal = 1 / 5 := by
  simp only [Qa, PMF.ofFintype_apply, Bool.false_eq_true, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Qa_true_toReal : (Qa true).toReal = 4 / 5 := by
  simp only [Qa, PMF.ofFintype_apply, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Pa'_false_toReal : (Pa' false).toReal = 2 / 3 := by
  simp only [Pa', PMF.ofFintype_apply, Bool.false_eq_true, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Pa'_true_toReal : (Pa' true).toReal = 1 / 3 := by
  simp only [Pa', PMF.ofFintype_apply, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Qa'_false_toReal : (Qa' false).toReal = 1 / 3 := by
  simp only [Qa', PMF.ofFintype_apply, Bool.false_eq_true, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Qa'_true_toReal : (Qa' true).toReal = 2 / 3 := by
  simp only [Qa', PMF.ofFintype_apply, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

/-- Case (a): the `Pa → Qa` approximate bound at `(log 2, 2/5)`. -/
theorem approx_a_PQ : approxMaxDivLE Pa Qa (Real.log 2) (2 / 5) := by
  intro s
  simp only [exp_log_two]
  fin_cases s <;> simp <;> norm_num

/-- Case (a): the `Qa → Pa` approximate bound at `(log 2, 2/5)`. -/
theorem approx_a_QP : approxMaxDivLE Qa Pa (Real.log 2) (2 / 5) := by
  intro s
  simp only [exp_log_two]
  fin_cases s <;> simp <;> norm_num

/-- Case (a): pure bound `Pa' → Qa'`. -/
theorem maxDiv_a_PQ : maxDivLE Pa' Qa' (Real.log 2) := by
  intro w
  cases w <;> simp [exp_log_two] <;> norm_num

/-- Case (a): pure bound `Qa' → Pa'`. -/
theorem maxDiv_a_QP : maxDivLE Qa' Pa' (Real.log 2) := by
  intro w
  cases w <;> simp [exp_log_two] <;> norm_num

/-- Case (a): `tvDist Pa Pa' = 2/15`. -/
theorem tvDist_a_P : tvDist Pa Pa' = 2 / 15 := by
  show (1 / 2) * ∑ w, |(Pa w).toReal - (Pa' w).toReal| = 2 / 15
  simp only [Fintype.sum_bool, Pa_false_toReal, Pa_true_toReal,
    Pa'_false_toReal, Pa'_true_toReal]
  norm_num

/-- Case (a): `tvDist Qa Qa' = 2/15`. -/
theorem tvDist_a_Q : tvDist Qa Qa' = 2 / 15 := by
  show (1 / 2) * ∑ w, |(Qa w).toReal - (Qa' w).toReal| = 2 / 15
  simp only [Fintype.sum_bool, Qa_false_toReal, Qa_true_toReal,
    Qa'_false_toReal, Qa'_true_toReal]
  norm_num

/-- Case (a): `tvDist Pa Pa' ≤ δ / (exp ε + 1)`. -/
theorem tvDist_a_P_le :
    tvDist Pa Pa' ≤ (2 / 5) / (Real.exp (Real.log 2) + 1) := by
  rw [tvDist_a_P, exp_log_two]
  norm_num

/-- Case (a): `tvDist Qa Qa' ≤ δ / (exp ε + 1)`. -/
theorem tvDist_a_Q_le :
    tvDist Qa Qa' ≤ (2 / 5) / (Real.exp (Real.log 2) + 1) := by
  rw [tvDist_a_Q, exp_log_two]
  norm_num

/-- Case (a) forward through the iff: the bounds yield witnesses. -/
theorem iff_a_forward :
    ∃ P' Q', tvDist Pa P' ≤ (2 / 5) / (Real.exp (Real.log 2) + 1) ∧
      tvDist Qa Q' ≤ (2 / 5) / (Real.exp (Real.log 2) + 1) ∧
      maxDivLE P' Q' (Real.log 2) ∧ maxDivLE Q' P' (Real.log 2) :=
  (approxMaxDivLE_both_iff_exists_repair Pa Qa (Real.log 2) (2 / 5)
    log_two_nonneg (by norm_num)).mp ⟨approx_a_PQ, approx_a_QP⟩

/-- Case (a) backward through the iff: the witnesses give the bounds. -/
theorem iff_a_backward :
    approxMaxDivLE Pa Qa (Real.log 2) (2 / 5) ∧
      approxMaxDivLE Qa Pa (Real.log 2) (2 / 5) :=
  (approxMaxDivLE_both_iff_exists_repair Pa Qa (Real.log 2) (2 / 5)
    log_two_nonneg (by norm_num)).mpr
    ⟨Pa', Qa', tvDist_a_P_le, tvDist_a_Q_le, maxDiv_a_PQ, maxDiv_a_QP⟩

/-- Case (b): `Pb = (9/10, 1/10)` on `Bool` (`false` first). -/
noncomputable def Pb : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal (1 / 10) else ENNReal.ofReal (9 / 10)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- Case (b): `Qb = (3/10, 7/10)` on `Bool`. -/
noncomputable def Qb : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal (7 / 10) else ENNReal.ofReal (3 / 10)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- Case (b) witness: `Pb' = (11/15, 4/15)`. -/
noncomputable def Pb' : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal (4 / 15) else ENNReal.ofReal (11 / 15)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- Case (b) witness: `Qb' = (7/15, 8/15)`. -/
noncomputable def Qb' : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ENNReal.ofReal (8 / 15) else ENNReal.ofReal (7 / 15)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

@[simp]
theorem Pb_false_toReal : (Pb false).toReal = 9 / 10 := by
  simp only [Pb, PMF.ofFintype_apply, Bool.false_eq_true, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Pb_true_toReal : (Pb true).toReal = 1 / 10 := by
  simp only [Pb, PMF.ofFintype_apply, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Qb_false_toReal : (Qb false).toReal = 3 / 10 := by
  simp only [Qb, PMF.ofFintype_apply, Bool.false_eq_true, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Qb_true_toReal : (Qb true).toReal = 7 / 10 := by
  simp only [Qb, PMF.ofFintype_apply, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Pb'_false_toReal : (Pb' false).toReal = 11 / 15 := by
  simp only [Pb', PMF.ofFintype_apply, Bool.false_eq_true, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Pb'_true_toReal : (Pb' true).toReal = 4 / 15 := by
  simp only [Pb', PMF.ofFintype_apply, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Qb'_false_toReal : (Qb' false).toReal = 7 / 15 := by
  simp only [Qb', PMF.ofFintype_apply, Bool.false_eq_true, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Qb'_true_toReal : (Qb' true).toReal = 8 / 15 := by
  simp only [Qb', PMF.ofFintype_apply, ↓reduceIte]
  exact ENNReal.toReal_ofReal (by norm_num)

/-- Case (b): the `Pb → Qb` approximate bound at `(log 2, 1/2)`. -/
theorem approx_b_PQ : approxMaxDivLE Pb Qb (Real.log 2) (1 / 2) := by
  intro s
  simp only [exp_log_two]
  fin_cases s <;> simp <;> norm_num

/-- Case (b): the `Qb → Pb` approximate bound at `(log 2, 1/2)`. -/
theorem approx_b_QP : approxMaxDivLE Qb Pb (Real.log 2) (1 / 2) := by
  intro s
  simp only [exp_log_two]
  fin_cases s <;> simp <;> norm_num

/-- Case (b): pure bound `Pb' → Qb'`. -/
theorem maxDiv_b_PQ : maxDivLE Pb' Qb' (Real.log 2) := by
  intro w
  cases w <;> simp [exp_log_two] <;> norm_num

/-- Case (b): pure bound `Qb' → Pb'`. -/
theorem maxDiv_b_QP : maxDivLE Qb' Pb' (Real.log 2) := by
  intro w
  cases w <;> simp [exp_log_two] <;> norm_num

/-- Case (b): `tvDist Pb Pb' = 1/6`. -/
theorem tvDist_b_P : tvDist Pb Pb' = 1 / 6 := by
  show (1 / 2) * ∑ w, |(Pb w).toReal - (Pb' w).toReal| = 1 / 6
  simp only [Fintype.sum_bool, Pb_false_toReal, Pb_true_toReal,
    Pb'_false_toReal, Pb'_true_toReal]
  norm_num

/-- Case (b): `tvDist Qb Qb' = 1/6`. -/
theorem tvDist_b_Q : tvDist Qb Qb' = 1 / 6 := by
  show (1 / 2) * ∑ w, |(Qb w).toReal - (Qb' w).toReal| = 1 / 6
  simp only [Fintype.sum_bool, Qb_false_toReal, Qb_true_toReal,
    Qb'_false_toReal, Qb'_true_toReal]
  norm_num

/-- Case (b): `tvDist Pb Pb' ≤ δ / (exp ε + 1)`. -/
theorem tvDist_b_P_le :
    tvDist Pb Pb' ≤ (1 / 2) / (Real.exp (Real.log 2) + 1) := by
  rw [tvDist_b_P, exp_log_two]
  norm_num

/-- Case (b): `tvDist Qb Qb' ≤ δ / (exp ε + 1)`. -/
theorem tvDist_b_Q_le :
    tvDist Qb Qb' ≤ (1 / 2) / (Real.exp (Real.log 2) + 1) := by
  rw [tvDist_b_Q, exp_log_two]
  norm_num

/-- Case (b) forward through the iff: the bounds yield witnesses. -/
theorem iff_b_forward :
    ∃ P' Q', tvDist Pb P' ≤ (1 / 2) / (Real.exp (Real.log 2) + 1) ∧
      tvDist Qb Q' ≤ (1 / 2) / (Real.exp (Real.log 2) + 1) ∧
      maxDivLE P' Q' (Real.log 2) ∧ maxDivLE Q' P' (Real.log 2) :=
  (approxMaxDivLE_both_iff_exists_repair Pb Qb (Real.log 2) (1 / 2)
    log_two_nonneg (by norm_num)).mp ⟨approx_b_PQ, approx_b_QP⟩

/-- Case (b) backward through the iff: the witnesses give the bounds. -/
theorem iff_b_backward :
    approxMaxDivLE Pb Qb (Real.log 2) (1 / 2) ∧
      approxMaxDivLE Qb Pb (Real.log 2) (1 / 2) :=
  (approxMaxDivLE_both_iff_exists_repair Pb Qb (Real.log 2) (1 / 2)
    log_two_nonneg (by norm_num)).mpr
    ⟨Pb', Qb', tvDist_b_P_le, tvDist_b_Q_le, maxDiv_b_PQ, maxDiv_b_QP⟩

/-- Case (c): at `delta = 0`, the forward direction yields witnesses with
`tvDist ≤ 0` on both sides. -/
theorem delta_zero_forward {Outcome : Type*} [Fintype Outcome]
    [Nonempty Outcome] (P : PMF Outcome) :
    ∃ P' Q', tvDist P P' ≤ 0 ∧ tvDist P Q' ≤ 0 ∧
      maxDivLE P' Q' (Real.log 2) ∧ maxDivLE Q' P' (Real.log 2) := by
  have hself : approxMaxDivLE P P (Real.log 2) 0 :=
    CSLibExtTest.Privacy.MaxDivergenceDecompositionTests.approx_self_of_nonneg
      P (Real.log 2) log_two_nonneg
  obtain ⟨P', Q', htvP, htvQ, hmaxPQ, hmaxQP⟩ :=
    (approxMaxDivLE_both_iff_exists_repair P P (Real.log 2) 0
      log_two_nonneg le_rfl).mp ⟨hself, hself⟩
  exact ⟨P', Q', by simpa using htvP, by simpa using htvQ, hmaxPQ, hmaxQP⟩

#print axioms CSLibExt.Privacy.MaxDivergenceDecomposition.approxMaxDivLE_both_iff_exists_repair

end CSLibExtTest.Privacy.MaxDivergenceDecompositionPart2Tests
