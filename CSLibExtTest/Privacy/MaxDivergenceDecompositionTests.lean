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

/-
Dominated-repair tests for
`exists_dominated_pure_pair_of_approxMaxDivLE_both` on `Fin 2`:
(a) `P = Q` at `delta = 0`, (b) `eps = 0` with `P ≠ Q`,
(c) `eps = Real.log 2` with `P ≠ Q`.
-/

namespace CSLibExtTest.Privacy.MaxDivergenceDecompositionDominatedTests

open CSLibExt.Privacy.MaxDivergenceDecomposition

/-- `PFinA = (3/4, 1/4)` on `Fin 2`. -/
noncomputable def PFinA : PMF (Fin 2) :=
  PMF.ofFintype ![ENNReal.ofReal (3 / 4), ENNReal.ofReal (1 / 4)] (by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- `QFinA = (1/2, 1/2)` on `Fin 2`. -/
noncomputable def QFinA : PMF (Fin 2) :=
  PMF.ofFintype ![ENNReal.ofReal (1 / 2), ENNReal.ofReal (1 / 2)] (by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

@[simp]
theorem PFinA_zero_toReal : (PFinA 0).toReal = 3 / 4 := by
  simp only [PFinA, PMF.ofFintype_apply, Matrix.cons_val_zero]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem PFinA_one_toReal : (PFinA 1).toReal = 1 / 4 := by
  simp only [PFinA, PMF.ofFintype_apply, Matrix.cons_val_one]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem QFinA_zero_toReal : (QFinA 0).toReal = 1 / 2 := by
  simp only [QFinA, PMF.ofFintype_apply, Matrix.cons_val_zero]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem QFinA_one_toReal : (QFinA 1).toReal = 1 / 2 := by
  simp only [QFinA, PMF.ofFintype_apply, Matrix.cons_val_one]
  exact ENNReal.toReal_ofReal (by norm_num)

theorem PFinA_ne_QFinA : PFinA ≠ QFinA := by
  intro h
  have h0 : (PFinA 0).toReal = (QFinA 0).toReal :=
    congrArg (fun P => (P 0).toReal) h
  simp only [PFinA_zero_toReal, QFinA_zero_toReal] at h0
  norm_num at h0

/-- Case (a): self bound at `(0, 0)`. -/
theorem approx_domA : approxMaxDivLE PFinA PFinA 0 0 :=
  CSLibExtTest.Privacy.MaxDivergenceDecompositionTests.approx_self_of_nonneg
    PFinA 0 (by norm_num)

/-- Case (a): domination at each atom is the pointwise bound. -/
theorem domA_atoms :
    ∃ P₀ Q₀ : PMF (Fin 2),
      (P₀ 0).toReal ≤ (PFinA 0).toReal ∧
      (P₀ 1).toReal ≤ (PFinA 1).toReal ∧
      (Q₀ 0).toReal ≤ (PFinA 0).toReal ∧
      (Q₀ 1).toReal ≤ (PFinA 1).toReal := by
  obtain ⟨P₀, Q₀, _, _, hdomP, hdomQ⟩ :=
    exists_dominated_pure_pair_of_approxMaxDivLE_both PFinA PFinA 0 0
      (by norm_num) (by norm_num) (by norm_num) approx_domA approx_domA
  refine ⟨P₀, Q₀, ?_, ?_, ?_, ?_⟩
  · have h := hdomP 0; simpa using h
  · have h := hdomP 1; simpa using h
  · have h := hdomQ 0; simpa using h
  · have h := hdomQ 1; simpa using h

/-- Case (b): the `PFinA → QFinA` bound at `(0, 1/4)`. -/
theorem approx_domB_PQ : approxMaxDivLE PFinA QFinA 0 (1 / 4) := by
  intro s
  simp only [Real.exp_zero, one_mul]
  fin_cases s <;> simp <;> norm_num

/-- Case (b): the `QFinA → PFinA` bound at `(0, 1/4)`. -/
theorem approx_domB_QP : approxMaxDivLE QFinA PFinA 0 (1 / 4) := by
  intro s
  simp only [Real.exp_zero, one_mul]
  fin_cases s <;> simp <;> norm_num

/-- Case (b): two-sided pure bounds at `eps = 0` give pointwise equality. -/
theorem domB_eq (P₀ Q₀ : PMF (Fin 2)) (hPQ : maxDivLE P₀ Q₀ 0)
    (hQP : maxDivLE Q₀ P₀ 0) (w : Fin 2) :
    (P₀ w).toReal = (Q₀ w).toReal := by
  have h1 := hPQ w
  have h2 := hQP w
  simp only [Real.exp_zero, one_mul] at h1 h2
  exact le_antisymm h1 h2

/-- Case (b): witnesses agree at each atom. -/
theorem domB_atoms :
    ∃ P₀ Q₀ : PMF (Fin 2),
      (P₀ 0).toReal = (Q₀ 0).toReal ∧ (P₀ 1).toReal = (Q₀ 1).toReal := by
  obtain ⟨P₀, Q₀, hPQ, hQP, _, _⟩ :=
    exists_dominated_pure_pair_of_approxMaxDivLE_both PFinA QFinA 0 (1 / 4)
      (by norm_num) (by norm_num) (by norm_num) approx_domB_PQ approx_domB_QP
  exact ⟨P₀, Q₀, domB_eq P₀ Q₀ hPQ hQP 0, domB_eq P₀ Q₀ hPQ hQP 1⟩

/-- `Real.exp (Real.log 2) = 2`. -/
theorem exp_log_two_dom : Real.exp (Real.log 2) = 2 :=
  Real.exp_log (by norm_num)

/-- `Real.log 2` is nonnegative. -/
theorem log_two_nonneg_dom : 0 ≤ Real.log 2 :=
  Real.log_nonneg (by norm_num)

/-- Case (c): `PFinC = (4/5, 1/5)` on `Fin 2`. -/
noncomputable def PFinC : PMF (Fin 2) :=
  PMF.ofFintype ![ENNReal.ofReal (4 / 5), ENNReal.ofReal (1 / 5)] (by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- Case (c): `QFinC = (1/5, 4/5)` on `Fin 2`. -/
noncomputable def QFinC : PMF (Fin 2) :=
  PMF.ofFintype ![ENNReal.ofReal (1 / 5), ENNReal.ofReal (4 / 5)] (by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

@[simp]
theorem PFinC_zero_toReal : (PFinC 0).toReal = 4 / 5 := by
  simp only [PFinC, PMF.ofFintype_apply, Matrix.cons_val_zero]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem PFinC_one_toReal : (PFinC 1).toReal = 1 / 5 := by
  simp only [PFinC, PMF.ofFintype_apply, Matrix.cons_val_one]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem QFinC_zero_toReal : (QFinC 0).toReal = 1 / 5 := by
  simp only [QFinC, PMF.ofFintype_apply, Matrix.cons_val_zero]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem QFinC_one_toReal : (QFinC 1).toReal = 4 / 5 := by
  simp only [QFinC, PMF.ofFintype_apply, Matrix.cons_val_one]
  exact ENNReal.toReal_ofReal (by norm_num)

theorem PFinC_ne_QFinC : PFinC ≠ QFinC := by
  intro h
  have h0 : (PFinC 0).toReal = (QFinC 0).toReal :=
    congrArg (fun P => (P 0).toReal) h
  simp only [PFinC_zero_toReal, QFinC_zero_toReal] at h0
  norm_num at h0

/-- Case (c): the `PFinC → QFinC` bound at `(log 2, 2/5)`. -/
theorem approx_domC_PQ : approxMaxDivLE PFinC QFinC (Real.log 2) (2 / 5) := by
  intro s
  simp only [exp_log_two_dom]
  fin_cases s <;> simp <;> norm_num

/-- Case (c): the `QFinC → PFinC` bound at `(log 2, 2/5)`. -/
theorem approx_domC_QP : approxMaxDivLE QFinC PFinC (Real.log 2) (2 / 5) := by
  intro s
  simp only [exp_log_two_dom]
  fin_cases s <;> simp <;> norm_num

/-- Case (c): all four conclusions asserted at each atom. -/
theorem domC_atoms :
    ∃ P₀ Q₀ : PMF (Fin 2),
      (P₀ 0).toReal ≤ 2 * (Q₀ 0).toReal ∧
      (Q₀ 0).toReal ≤ 2 * (P₀ 0).toReal ∧
      (P₀ 1).toReal ≤ 2 * (Q₀ 1).toReal ∧
      (Q₀ 1).toReal ≤ 2 * (P₀ 1).toReal ∧
      (1 - 2 / 5) * (P₀ 0).toReal ≤ (PFinC 0).toReal ∧
      (1 - 2 / 5) * (P₀ 1).toReal ≤ (PFinC 1).toReal ∧
      (1 - 2 / 5) * (Q₀ 0).toReal ≤ (QFinC 0).toReal ∧
      (1 - 2 / 5) * (Q₀ 1).toReal ≤ (QFinC 1).toReal := by
  obtain ⟨P₀, Q₀, hPQ, hQP, hdomP, hdomQ⟩ :=
    exists_dominated_pure_pair_of_approxMaxDivLE_both PFinC QFinC (Real.log 2)
      (2 / 5) log_two_nonneg_dom (by norm_num) (by norm_num)
      approx_domC_PQ approx_domC_QP
  have e0 := hPQ 0
  have e1 := hPQ 1
  have f0 := hQP 0
  have f1 := hQP 1
  rw [exp_log_two_dom] at e0 e1 f0 f1
  exact ⟨P₀, Q₀, e0, f0, e1, f1, hdomP 0, hdomP 1, hdomQ 0, hdomQ 1⟩

/-
Asymmetric cases for `exists_dominated_pure_pair_of_approxMaxDivLE_both`:
(d) `PFinD = (2/5, 3/5)`, `QFinD = (4/5, 1/5)` at `(log 2, 1/5)`,
whose capped sums `4/5 < 1` lie in the `v > u` strict interpolation
branch; (e) the swapped pair `(QFinD, PFinD)`, covering `u > v`.
-/

/-- Case (d): `PFinD = (2/5, 3/5)` on `Fin 2`. -/
noncomputable def PFinD : PMF (Fin 2) :=
  PMF.ofFintype ![ENNReal.ofReal (2 / 5), ENNReal.ofReal (3 / 5)] (by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- Case (d): `QFinD = (4/5, 1/5)` on `Fin 2`. -/
noncomputable def QFinD : PMF (Fin 2) :=
  PMF.ofFintype ![ENNReal.ofReal (4 / 5), ENNReal.ofReal (1 / 5)] (by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

@[simp]
theorem PFinD_zero_toReal : (PFinD 0).toReal = 2 / 5 := by
  simp only [PFinD, PMF.ofFintype_apply, Matrix.cons_val_zero]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem PFinD_one_toReal : (PFinD 1).toReal = 3 / 5 := by
  simp only [PFinD, PMF.ofFintype_apply, Matrix.cons_val_one]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem QFinD_zero_toReal : (QFinD 0).toReal = 4 / 5 := by
  simp only [QFinD, PMF.ofFintype_apply, Matrix.cons_val_zero]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem QFinD_one_toReal : (QFinD 1).toReal = 1 / 5 := by
  simp only [QFinD, PMF.ofFintype_apply, Matrix.cons_val_one]
  exact ENNReal.toReal_ofReal (by norm_num)

/-- Case (d): capped sum `∑ w, capEnvelope PFinD QFinD (log 2) w = 4/5`. -/
theorem capSum_d_PQ :
    ∑ w, capEnvelope PFinD QFinD (Real.log 2) w = 4 / 5 := by
  have h0 : min ((2 : ℝ) / 5) (2 * (4 / 5)) = 2 / 5 :=
    min_eq_left (by norm_num)
  have h1 : min ((3 : ℝ) / 5) (2 * (1 / 5)) = 2 * (1 / 5) :=
    min_eq_right (by norm_num)
  rw [Fin.sum_univ_two]
  simp only [capEnvelope, exp_log_two_dom, PFinD_zero_toReal,
    PFinD_one_toReal, QFinD_zero_toReal, QFinD_one_toReal, h0, h1]
  norm_num

/-- Case (d): capped sum `∑ w, capEnvelope QFinD PFinD (log 2) w = 1`. -/
theorem capSum_d_QP :
    ∑ w, capEnvelope QFinD PFinD (Real.log 2) w = 1 := by
  have h0 : min ((4 : ℝ) / 5) (2 * (2 / 5)) = 4 / 5 :=
    min_eq_left (by norm_num)
  have h1 : min ((1 : ℝ) / 5) (2 * (3 / 5)) = 1 / 5 :=
    min_eq_left (by norm_num)
  rw [Fin.sum_univ_two]
  simp only [capEnvelope, exp_log_two_dom, PFinD_zero_toReal,
    PFinD_one_toReal, QFinD_zero_toReal, QFinD_one_toReal, h0, h1]
  norm_num

/-- Case (d) lies in the `v > u` strict interpolation branch. -/
theorem capSum_d_strict :
    ∑ w, capEnvelope PFinD QFinD (Real.log 2) w <
      ∑ w, capEnvelope QFinD PFinD (Real.log 2) w := by
  rw [capSum_d_PQ, capSum_d_QP]
  norm_num

/-- Case (d): the `PFinD → QFinD` bound at `(log 2, 1/5)`. -/
theorem approx_domD_PQ : approxMaxDivLE PFinD QFinD (Real.log 2) (1 / 5) := by
  intro s
  simp only [exp_log_two_dom]
  fin_cases s <;> simp <;> norm_num

/-- Case (d): the `QFinD → PFinD` bound at `(log 2, 1/5)`. -/
theorem approx_domD_QP : approxMaxDivLE QFinD PFinD (Real.log 2) (1 / 5) := by
  intro s
  simp only [exp_log_two_dom]
  fin_cases s <;> simp <;> norm_num

/-- Case (d): all four conclusions asserted at each atom. -/
theorem domD_atoms :
    ∃ P₀ Q₀ : PMF (Fin 2),
      (P₀ 0).toReal ≤ 2 * (Q₀ 0).toReal ∧
      (Q₀ 0).toReal ≤ 2 * (P₀ 0).toReal ∧
      (P₀ 1).toReal ≤ 2 * (Q₀ 1).toReal ∧
      (Q₀ 1).toReal ≤ 2 * (P₀ 1).toReal ∧
      (1 - 1 / 5) * (P₀ 0).toReal ≤ (PFinD 0).toReal ∧
      (1 - 1 / 5) * (P₀ 1).toReal ≤ (PFinD 1).toReal ∧
      (1 - 1 / 5) * (Q₀ 0).toReal ≤ (QFinD 0).toReal ∧
      (1 - 1 / 5) * (Q₀ 1).toReal ≤ (QFinD 1).toReal := by
  obtain ⟨P₀, Q₀, hPQ, hQP, hdomP, hdomQ⟩ :=
    exists_dominated_pure_pair_of_approxMaxDivLE_both PFinD QFinD (Real.log 2)
      (1 / 5) log_two_nonneg_dom (by norm_num) (by norm_num)
      approx_domD_PQ approx_domD_QP
  have e0 := hPQ 0
  have e1 := hPQ 1
  have f0 := hQP 0
  have f1 := hQP 1
  rw [exp_log_two_dom] at e0 e1 f0 f1
  exact ⟨P₀, Q₀, e0, f0, e1, f1, hdomP 0, hdomP 1, hdomQ 0, hdomQ 1⟩

/-- Case (e): swapped capped sum `∑ w, capEnvelope QFinD PFinD (log 2) w = 1`. -/
theorem capSum_e_QP :
    ∑ w, capEnvelope QFinD PFinD (Real.log 2) w = 1 :=
  capSum_d_QP

/-- Case (e): swapped capped sum `∑ w, capEnvelope PFinD QFinD (log 2) w = 4/5`. -/
theorem capSum_e_PQ :
    ∑ w, capEnvelope PFinD QFinD (Real.log 2) w = 4 / 5 :=
  capSum_d_PQ

/-- Case (e) lies in the `u > v` strict interpolation branch. -/
theorem capSum_e_strict :
    ∑ w, capEnvelope QFinD PFinD (Real.log 2) w >
      ∑ w, capEnvelope PFinD QFinD (Real.log 2) w := by
  rw [capSum_d_QP, capSum_d_PQ]
  norm_num

/-- Case (e): all four conclusions asserted at each atom. -/
theorem domE_atoms :
    ∃ P₀ Q₀ : PMF (Fin 2),
      (P₀ 0).toReal ≤ 2 * (Q₀ 0).toReal ∧
      (Q₀ 0).toReal ≤ 2 * (P₀ 0).toReal ∧
      (P₀ 1).toReal ≤ 2 * (Q₀ 1).toReal ∧
      (Q₀ 1).toReal ≤ 2 * (P₀ 1).toReal ∧
      (1 - 1 / 5) * (P₀ 0).toReal ≤ (QFinD 0).toReal ∧
      (1 - 1 / 5) * (P₀ 1).toReal ≤ (QFinD 1).toReal ∧
      (1 - 1 / 5) * (Q₀ 0).toReal ≤ (PFinD 0).toReal ∧
      (1 - 1 / 5) * (Q₀ 1).toReal ≤ (PFinD 1).toReal := by
  obtain ⟨P₀, Q₀, hPQ, hQP, hdomP, hdomQ⟩ :=
    exists_dominated_pure_pair_of_approxMaxDivLE_both QFinD PFinD (Real.log 2)
      (1 / 5) log_two_nonneg_dom (by norm_num) (by norm_num)
      approx_domD_QP approx_domD_PQ
  have e0 := hPQ 0
  have e1 := hPQ 1
  have f0 := hQP 0
  have f1 := hQP 1
  rw [exp_log_two_dom] at e0 e1 f0 f1
  exact ⟨P₀, Q₀, e0, f0, e1, f1, hdomP 0, hdomP 1, hdomQ 0, hdomQ 1⟩

#print axioms CSLibExt.Privacy.MaxDivergenceDecomposition.exists_dominated_pure_pair_of_approxMaxDivLE_both

end CSLibExtTest.Privacy.MaxDivergenceDecompositionDominatedTests

namespace CSLibExtTest.Privacy.MaxDivergenceDecompositionCommonMassTests

open CSLibExt.Privacy.MaxDivergenceDecomposition

/-- `Pcm0 = (3/4, 1/4)` on `Fin 2`. -/
noncomputable def Pcm0 : PMF (Fin 2) :=
  PMF.ofFintype ![ENNReal.ofReal (3 / 4), ENNReal.ofReal (1 / 4)] (by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- `Qcm0 = (1/2, 1/2)` on `Fin 2`. -/
noncomputable def Qcm0 : PMF (Fin 2) :=
  PMF.ofFintype ![ENNReal.ofReal (1 / 2), ENNReal.ofReal (1 / 2)] (by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- `Pcm = (7/8, 1/8)` on `Fin 2`. -/
noncomputable def Pcm : PMF (Fin 2) :=
  PMF.ofFintype ![ENNReal.ofReal (7 / 8), ENNReal.ofReal (1 / 8)] (by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

/-- `Qcm = (3/4, 1/4)` on `Fin 2`. -/
noncomputable def Qcm : PMF (Fin 2) :=
  PMF.ofFintype ![ENNReal.ofReal (3 / 4), ENNReal.ofReal (1 / 4)] (by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

@[simp]
theorem Pcm0_zero_toReal : (Pcm0 0).toReal = 3 / 4 := by
  simp only [Pcm0, PMF.ofFintype_apply, Matrix.cons_val_zero]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Pcm0_one_toReal : (Pcm0 1).toReal = 1 / 4 := by
  simp only [Pcm0, PMF.ofFintype_apply, Matrix.cons_val_one]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Qcm0_zero_toReal : (Qcm0 0).toReal = 1 / 2 := by
  simp only [Qcm0, PMF.ofFintype_apply, Matrix.cons_val_zero]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Qcm0_one_toReal : (Qcm0 1).toReal = 1 / 2 := by
  simp only [Qcm0, PMF.ofFintype_apply, Matrix.cons_val_one]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Pcm_zero_toReal : (Pcm 0).toReal = 7 / 8 := by
  simp only [Pcm, PMF.ofFintype_apply, Matrix.cons_val_zero]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Pcm_one_toReal : (Pcm 1).toReal = 1 / 8 := by
  simp only [Pcm, PMF.ofFintype_apply, Matrix.cons_val_one]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Qcm_zero_toReal : (Qcm 0).toReal = 3 / 4 := by
  simp only [Qcm, PMF.ofFintype_apply, Matrix.cons_val_zero]
  exact ENNReal.toReal_ofReal (by norm_num)

@[simp]
theorem Qcm_one_toReal : (Qcm 1).toReal = 1 / 4 := by
  simp only [Qcm, PMF.ofFintype_apply, Matrix.cons_val_one]
  exact ENNReal.toReal_ofReal (by norm_num)

/-- Outer `P` dominates half the ideal mass. -/
theorem cm_hP : ∀ w, (1 / 2 : ℝ) * (Pcm0 w).toReal ≤ (Pcm w).toReal := by
  intro w
  fin_cases w <;> simp <;> norm_num

/-- Outer `Q` dominates half the ideal mass. -/
theorem cm_hQ : ∀ w, (1 / 2 : ℝ) * (Qcm0 w).toReal ≤ (Qcm w).toReal := by
  intro w
  fin_cases w <;> simp <;> norm_num

/-- Ideal bound at `(0, 1/4)`. -/
theorem cm_hideal : approxMaxDivLE Pcm0 Qcm0 0 (1 / 4) := by
  intro s
  simp only [Real.exp_zero, one_mul]
  fin_cases s <;> simp <;> norm_num

/-- Transferred conclusion at `alpha = 1/2`. -/
theorem cm_main : approxMaxDivLE Pcm Qcm 0 ((1 / 2) * (1 / 4) + 1 - (1 / 2)) :=
  approxMaxDivLE_of_common_mass Pcm Qcm Pcm0 Qcm0 (1 / 2) 0 (1 / 4)
    (by norm_num) cm_hP cm_hQ cm_hideal

/-- Independent check of the conclusion at all four `Fin 2` events. -/
theorem cm_direct : approxMaxDivLE Pcm Qcm 0 ((1 / 2) * (1 / 4) + 1 - (1 / 2)) := by
  intro s
  simp only [Real.exp_zero, one_mul]
  fin_cases s <;> simp <;> norm_num

/-- The applied conclusion instantiated at the full event. -/
theorem cm_at_univ : ∑ w ∈ Finset.univ, (Pcm w).toReal ≤
    Real.exp 0 * ∑ w ∈ Finset.univ, (Qcm w).toReal +
      ((1 / 2) * (1 / 4) + 1 - (1 / 2)) :=
  cm_main Finset.univ

/-- At `alpha = 1` the transferred budget is exactly the ideal budget. -/
theorem cm_one_delta : ((1 : ℝ) * (1 / 4) + 1 - 1) = 1 / 4 := by norm_num

theorem cm_one : approxMaxDivLE Pcm0 Qcm0 0 (1 / 4) := by
  have h := approxMaxDivLE_of_common_mass Pcm0 Qcm0 Pcm0 Qcm0 (1 : ℝ) 0 (1 / 4)
    (by norm_num) (by intro w; simp) (by intro w; simp) cm_hideal
  rw [cm_one_delta] at h
  exact h

#print axioms CSLibExt.Privacy.MaxDivergenceDecomposition.approxMaxDivLE_of_common_mass

end CSLibExtTest.Privacy.MaxDivergenceDecompositionCommonMassTests
