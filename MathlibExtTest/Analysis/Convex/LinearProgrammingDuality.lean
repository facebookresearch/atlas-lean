/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.LinearProgrammingDuality

/-!
# Tests for strong linear programming duality

Focused checks for `LPDuality.strong_linear_programming_duality`: an ordinary
one-dimensional program whose optimum value is pinned down, plus the two
empty-index boundary cases (no primal variables, no constraints).
-/

@[expose]
public section

namespace LinearProgrammingDualityTest

/-- Constraint matrix `(1)` of the one-dimensional test program, given an
explicit matrix type so that dot notation resolves to `Matrix.mulVec`. -/
private def oneDimA : Matrix (Fin 1) (Fin 1) ℝ := ![![1]]

/-- The constraint matrix acts as the identity. -/
private theorem oneDimA_mulVec (x : Fin 1 → ℝ) (j : Fin 1) :
    oneDimA.mulVec x j = x 0 := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  simp [oneDimA, Matrix.mulVec, dotProduct]

/-- The transposed constraint matrix acts as the identity. -/
private theorem oneDimA_transpose_mulVec (y : Fin 1 → ℝ) (i : Fin 1) :
    (oneDimA.transpose.mulVec y) i = y 0 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  unfold oneDimA
  have h11 : (Matrix.transpose (![![1]] : Matrix (Fin 1) (Fin 1) ℝ)) 0 0 = 1 := rfl
  simp [Matrix.mulVec, dotProduct, h11]

/-- One-dimensional program `max { 2 * x | 0 ≤ x ≤ 5 }`: feasible and bounded. -/
private theorem oneDim_feas :
    ∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, oneDimA.mulVec x j ≤ ![5] j := by
  refine ⟨![5], Fin.forall_fin_one.mpr ?_, fun j => ?_⟩
  · simp
  · rw [oneDimA_mulVec]
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp

/-- One-dimensional program `max { 2 * x | 0 ≤ x ≤ 5 }`: bounded above by `10`. -/
private theorem oneDim_bdd (x : Fin 1 → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hAx : ∀ j, oneDimA.mulVec x j ≤ ![5] j) :
    (fun _ => (2 : ℝ)) ⬝ᵥ x ≤ 10 := by
  have h5 : x 0 ≤ 5 := by
    have h := hAx 0
    rw [oneDimA_mulVec] at h
    simpa using h
  have hnn : 0 ≤ x 0 := hx 0
  have hval : (fun _ => (2 : ℝ)) ⬝ᵥ x = 2 * x 0 := by
    simp [dotProduct]
  rw [hval]
  linarith

/-- One-dimensional optimum: the attained value equals `10`. -/
example :
    ∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧
      (∀ j, oneDimA.mulVec x j ≤ ![5] j) ∧
      (fun _ => (2 : ℝ)) ⬝ᵥ x = 10 := by
  obtain ⟨x, y, hx, hAx, hy, hAy, heq⟩ :=
    MathlibExt.Analysis.Convex.LPDuality.strong_linear_programming_duality
      oneDimA ![5] (fun _ => 2)
      oneDim_feas ⟨10, oneDim_bdd⟩
  have hxx : x 0 ≤ 5 := by
    have h := hAx 0
    rw [oneDimA_mulVec] at h
    simpa using h
  have hyy : 2 ≤ y 0 := by
    have h := hAy 0
    rw [oneDimA_transpose_mulVec] at h
    simpa using h
  have hval : (fun _ => (2 : ℝ)) ⬝ᵥ x = 2 * x 0 := by
    simp [dotProduct]
  refine ⟨x, hx, hAx, ?_⟩
  rw [hval]
  have hub : 2 * x 0 ≤ 10 := by linarith [hxx, hx 0]
  have hlb : 10 ≤ 2 * x 0 := by
    have hb : ![5] ⬝ᵥ y = 5 * y 0 := by
      simp [dotProduct]
    have hcc : (fun _ => (2 : ℝ)) ⬝ᵥ x = 2 * x 0 := hval
    rw [hcc, hb] at heq
    linarith [hyy, hy 0]
  linarith

/-- No primal variables (`n = 0`): feasible and bounded, hence optimal pair. -/
example :
    ∃ x : Fin 0 → ℝ, ∃ y : Fin 1 → ℝ,
      (∀ i, 0 ≤ x i) ∧
      (∀ j, (0 : Matrix (Fin 1) (Fin 0) ℝ).mulVec x j ≤ ![7] j) ∧
      (∀ j, 0 ≤ y j) ∧
      (∀ i, (0 : Fin 0 → ℝ) i ≤
        ((0 : Matrix (Fin 1) (Fin 0) ℝ).transpose.mulVec y) i) ∧
      (0 : Fin 0 → ℝ) ⬝ᵥ x = ![7] ⬝ᵥ y := by
  apply MathlibExt.Analysis.Convex.LPDuality.strong_linear_programming_duality
  · exact ⟨0, fun i => i.elim0, Fin.forall_fin_one.mpr (by simp)⟩
  · exact ⟨0, fun x _ _ => by simp⟩

/-- No constraints (`m = 0`): feasible and bounded, hence optimal pair. -/
example :
    ∃ x : Fin 1 → ℝ, ∃ y : Fin 0 → ℝ,
      (∀ i, 0 ≤ x i) ∧
      (∀ j, (0 : Matrix (Fin 0) (Fin 1) ℝ).mulVec x j ≤ ![] j) ∧
      (∀ j, 0 ≤ y j) ∧
      (∀ i, (![0] : Fin 1 → ℝ) i ≤
        ((0 : Matrix (Fin 0) (Fin 1) ℝ).transpose.mulVec y) i) ∧
      (![0] : Fin 1 → ℝ) ⬝ᵥ x = ![] ⬝ᵥ y := by
  apply MathlibExt.Analysis.Convex.LPDuality.strong_linear_programming_duality
  · exact ⟨0, fun i => by simp, fun j => j.elim0⟩
  · exact ⟨0, fun x _ _ => by simp [dotProduct]⟩

/-- Fixture matrix `[[1, 1]]`, shared by FX01 (F1) and FX08 (F2). -/
private def exA11 : Matrix (Fin 1) (Fin 2) ℝ := ![![1, 1]]

/-- Fixture matrix `[[1]]`, shared by FX02 (F1) and FX10 (F2). -/
private def exA1 : Matrix (Fin 1) (Fin 1) ℝ := ![![1]]

/-- Fixture matrix `[[-1]]` for the F1 sign tests (FX03). -/
private def exANeg : Matrix (Fin 1) (Fin 1) ℝ := ![![-1]]

/-- Fixture matrix `[[1], [1]]` for the F2 certificate test (FX09). -/
private def exACol : Matrix (Fin 2) (Fin 1) ℝ := ![![1], ![1]]

/-- Fixture matrix `[[0, 0]]` for the F2 zero-row test (FX11). -/
private def exAZero : Matrix (Fin 1) (Fin 2) ℝ := ![![0, 0]]

/-- FX01 witness: `x = (1, 0)` is nonnegative with `A x = (1) ≤ (1)`. -/
private theorem f1Pos_feas :
    ∃ x : Fin 2 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, exA11.mulVec x j ≤ ![1] j := by
  refine ⟨![1, 0], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [exA11, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- FX01 forward: F1 applied to the feasible witness gives `0 ≤ b ⬝ᵥ y`
for the admissible `y = (2)`; concretely `b ⬝ᵥ y = 2`. -/
private theorem f1Pos_dual :
    0 ≤ (![1] : Fin 1 → ℝ) ⬝ᵥ ![2] ∧ (![1] : Fin 1 → ℝ) ⬝ᵥ ![2] = 2 := by
  have hF1 := Matrix.exists_nonneg_mulVec_le_iff exA11 (![1] : Fin 1 → ℝ)
  have hy : ∀ j : Fin 1, 0 ≤ (![2] : Fin 1 → ℝ) j := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp
  have hAty : ∀ i : Fin 2, 0 ≤ (exA11.transpose.mulVec ![2]) i := by
    have h00 : exA11 0 0 = 1 := by simp [exA11]
    have h01 : exA11 0 1 = 1 := by simp [exA11]
    intro i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, h00]
    · simp [Matrix.mulVec, dotProduct, h01]
  have hpos := hF1.mp f1Pos_feas ![2] hy hAty
  have hdot : (![1] : Fin 1 → ℝ) ⬝ᵥ ![2] = 2 := by simp [dotProduct]
  exact ⟨hpos, hdot⟩

/-- FX02 certificate: `A = [[1]]`, `b = (-1)` is infeasible via F1 with
`y = (1)`, since `Aᵀ y = (1) ≥ 0` and `b ⬝ᵥ y = -1 < 0`. -/
private theorem f1Cert_infeasible :
    ¬ ∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, exA1.mulVec x j ≤ ![-1] j := by
  intro hfeas
  have hF1 := Matrix.exists_nonneg_mulVec_le_iff exA1 (![-1] : Fin 1 → ℝ)
  have hy : ∀ j : Fin 1, 0 ≤ (![1] : Fin 1 → ℝ) j := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp
  have hAty : ∀ i : Fin 1, 0 ≤ (exA1.transpose.mulVec ![1]) i := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h00 : exA1 0 0 = 1 := by simp [exA1]
    simp [Matrix.mulVec, dotProduct, h00]
  have hpos := hF1.mp hfeas ![1] hy hAty
  have hneg : (![-1] : Fin 1 → ℝ) ⬝ᵥ ![1] < 0 := by norm_num [dotProduct]
  linarith

/-- FX02 converse: from the elementary infeasibility of `x ≥ 0` with
`x ≤ -1`, F1 backward yields a certificate `y ≥ 0` with `Aᵀ y ≥ 0`
and `b ⬝ᵥ y < 0`. -/
private theorem f1Converse_cert :
    ∃ y : Fin 1 → ℝ, (∀ j, 0 ≤ y j) ∧
      (∀ i, 0 ≤ (exA1.transpose.mulVec y) i) ∧
      (![-1] : Fin 1 → ℝ) ⬝ᵥ y < 0 := by
  have hne : ¬ ∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, exA1.mulVec x j ≤ ![-1] j := by
    rintro ⟨x, hx, hAx⟩
    have hentry : exA1 0 0 = 1 := by simp [exA1]
    have hAx0 : (exA1.mulVec x) 0 = x 0 := by
      simp [Matrix.mulVec, dotProduct, hentry]
    have h0 := hAx 0
    rw [hAx0] at h0
    have h1 : (![-1] : Fin 1 → ℝ) 0 = -1 := by simp
    rw [h1] at h0
    linarith [hx 0]
  have hF1 := Matrix.exists_nonneg_mulVec_le_iff exA1 (![-1] : Fin 1 → ℝ)
  have hnotRHS : ¬ ∀ y : Fin 1 → ℝ, (∀ j, 0 ≤ y j) →
      (∀ i, 0 ≤ (exA1.transpose.mulVec y) i) →
      0 ≤ (![-1] : Fin 1 → ℝ) ⬝ᵥ y := fun hrhs => hne (hF1.mpr hrhs)
  push Not at hnotRHS
  exact hnotRHS

/-- FX03 feasibility: `A = [[-1]]`, `b = (1)` is witnessed by `x = 0`. -/
private theorem f1Sign_feas :
    ∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, exANeg.mulVec x j ≤ ![1] j := by
  refine ⟨![0], ?_, ?_⟩
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [Matrix.mulVec, dotProduct]

/-- FX03 counterfactual: the unsigned `y = (-1)` has `Aᵀ y = (1) ≥ 0`
and `b ⬝ᵥ y = -1 < 0`, violating only `y ≥ 0`. -/
private theorem f1Sign_unsigned :
    (∀ i : Fin 1, 0 ≤ (exANeg.transpose.mulVec ![-1]) i) ∧
    (![1] : Fin 1 → ℝ) ⬝ᵥ ![-1] < 0 ∧
    ¬ ∀ j : Fin 1, 0 ≤ (![-1] : Fin 1 → ℝ) j := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h00 : exANeg 0 0 = -1 := by simp [exANeg]
    simp [Matrix.mulVec, dotProduct, h00]
  · norm_num [dotProduct]
  · intro hall
    have heq : (![-1] : Fin 1 → ℝ) 0 = -1 := by simp
    have h0 := hall 0
    rw [heq] at h0
    norm_num at h0

/-- FX03 as an F2 certificate: the same `y = (-1)` shows the equality
system `-x = 1` has no `x ≥ 0`. -/
private theorem f1Sign_eqInfeasible :
    ¬ ∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧ exANeg.mulVec x = ![1] := by
  intro hfeas
  have hF2 := Matrix.exists_nonneg_mulVec_eq_iff exANeg (![1] : Fin 1 → ℝ)
  have hpos := hF2.mp hfeas ![-1] f1Sign_unsigned.1
  have hneg : (![1] : Fin 1 → ℝ) ⬝ᵥ ![-1] < 0 := f1Sign_unsigned.2.1
  linarith

/-- FX04: with no constraints (`m = 0`, `n = 2`), both sides hold. -/
private theorem f1EmptyRows_both :
    (∃ x : Fin 2 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j : Fin 0, (0 : Matrix (Fin 0) (Fin 2) ℝ).mulVec x j ≤ ![] j) ∧
    (∀ y : Fin 0 → ℝ, (∀ j, 0 ≤ y j) →
      (∀ i, 0 ≤ ((0 : Matrix (Fin 0) (Fin 2) ℝ).transpose.mulVec y) i) →
      0 ≤ (![] : Fin 0 → ℝ) ⬝ᵥ y) := by
  have hLHS : ∃ x : Fin 2 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j : Fin 0, (0 : Matrix (Fin 0) (Fin 2) ℝ).mulVec x j ≤ ![] j :=
    ⟨![0, 0], fun i => by fin_cases i <;> simp, fun j => j.elim0⟩
  have hF1 := Matrix.exists_nonneg_mulVec_le_iff
    (0 : Matrix (Fin 0) (Fin 2) ℝ) (![] : Fin 0 → ℝ)
  exact ⟨hLHS, hF1.mp hLHS⟩

/-- FX05: with no variables (`n = 0`) and `b = (2, 0)`, feasible since
`A x = (0, 0) ≤ b`. -/
private theorem f1NoVars_feas :
    (∃ x : Fin 0 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, (0 : Matrix (Fin 2) (Fin 0) ℝ).mulVec x j ≤ ![2, 0] j) ∧
    (∀ y : Fin 2 → ℝ, (∀ j, 0 ≤ y j) →
      (∀ i : Fin 0,
        0 ≤ ((0 : Matrix (Fin 2) (Fin 0) ℝ).transpose.mulVec y) i) →
      0 ≤ (![2, 0] : Fin 2 → ℝ) ⬝ᵥ y) := by
  have hLHS : ∃ x : Fin 0 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, (0 : Matrix (Fin 2) (Fin 0) ℝ).mulVec x j ≤ ![2, 0] j := by
    refine ⟨0, fun i => i.elim0, ?_⟩
    intro j
    have hAx : ((0 : Matrix (Fin 2) (Fin 0) ℝ).mulVec 0) j = 0 := by
      simp [Matrix.mulVec, dotProduct]
    rw [hAx]
    fin_cases j <;> simp
  have hF1 := Matrix.exists_nonneg_mulVec_le_iff
    (0 : Matrix (Fin 2) (Fin 0) ℝ) (![2, 0] : Fin 2 → ℝ)
  exact ⟨hLHS, hF1.mp hLHS⟩

/-- FX06: with no variables (`n = 0`) and `b = (-1)`, infeasible with
F1 certificate `y = (1)`. -/
private theorem f1NoVars_infeasible :
    ¬ ∃ x : Fin 0 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, (0 : Matrix (Fin 1) (Fin 0) ℝ).mulVec x j ≤ ![-1] j := by
  intro hfeas
  have hF1 := Matrix.exists_nonneg_mulVec_le_iff
    (0 : Matrix (Fin 1) (Fin 0) ℝ) (![-1] : Fin 1 → ℝ)
  have hy : ∀ j : Fin 1, 0 ≤ (![1] : Fin 1 → ℝ) j := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp
  have hAty : ∀ i : Fin 0,
      0 ≤ ((0 : Matrix (Fin 1) (Fin 0) ℝ).transpose.mulVec ![1]) i :=
    fun i => i.elim0
  have hpos := hF1.mp hfeas ![1] hy hAty
  have hneg : (![-1] : Fin 1 → ℝ) ⬝ᵥ ![1] < 0 := by norm_num [dotProduct]
  linarith

/-- FX07: with `m = 0` and `n = 0`, both sides hold. -/
private theorem f1Empty_both :
    (∃ x : Fin 0 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j : Fin 0, (0 : Matrix (Fin 0) (Fin 0) ℝ).mulVec x j ≤ ![] j) ∧
    (∀ y : Fin 0 → ℝ, (∀ j, 0 ≤ y j) →
      (∀ i : Fin 0,
        0 ≤ ((0 : Matrix (Fin 0) (Fin 0) ℝ).transpose.mulVec y) i) →
      0 ≤ (![] : Fin 0 → ℝ) ⬝ᵥ y) := by
  have hLHS : ∃ x : Fin 0 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j : Fin 0, (0 : Matrix (Fin 0) (Fin 0) ℝ).mulVec x j ≤ ![] j :=
    ⟨0, fun i => i.elim0, fun j => j.elim0⟩
  have hF1 := Matrix.exists_nonneg_mulVec_le_iff
    (0 : Matrix (Fin 0) (Fin 0) ℝ) (![] : Fin 0 → ℝ)
  exact ⟨hLHS, hF1.mp hLHS⟩

/-- Empty right-hand side: with `m = 0` every `b ⬝ᵥ y` is `0`
(FX04, FX07, FX14). -/
private theorem noConstraints_dot (y : Fin 0 → ℝ) :
    (![] : Fin 0 → ℝ) ⬝ᵥ y = 0 := by
  simp [dotProduct]

/-- FX08 witness: `x = (1, 1)` is nonnegative with `A x = (2)`. -/
private theorem f2Pos_feas :
    ∃ x : Fin 2 → ℝ, (∀ i, 0 ≤ x i) ∧ exA11.mulVec x = ![2] := by
  refine ⟨![1, 1], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have hAx : (exA11.mulVec ![1, 1]) 0 = 2 := by
      norm_num [exA11, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hb : (![2] : Fin 1 → ℝ) 0 = 2 := by simp
    rw [hAx, hb]

/-- FX08 forward: F2 applied to the feasible witness gives `0 ≤ b ⬝ᵥ y`
for the admissible `y = (3)`; concretely `b ⬝ᵥ y = 6`. -/
private theorem f2Pos_dual :
    0 ≤ (![2] : Fin 1 → ℝ) ⬝ᵥ ![3] ∧ (![2] : Fin 1 → ℝ) ⬝ᵥ ![3] = 6 := by
  have hF2 := Matrix.exists_nonneg_mulVec_eq_iff exA11 (![2] : Fin 1 → ℝ)
  have hAty : ∀ i : Fin 2, 0 ≤ (exA11.transpose.mulVec ![3]) i := by
    have h00 : exA11 0 0 = 1 := by simp [exA11]
    have h01 : exA11 0 1 = 1 := by simp [exA11]
    intro i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, h00]
    · simp [Matrix.mulVec, dotProduct, h01]
  have hpos := hF2.mp f2Pos_feas ![3] hAty
  have hdot : (![2] : Fin 1 → ℝ) ⬝ᵥ ![3] = 6 := by norm_num [dotProduct]
  exact ⟨hpos, hdot⟩

/-- FX09 (V2): the inconsistent system with rows `x = 1` and `x = 2` is
infeasible via the sign-free certificate `y = (1, -1)`, since
`Aᵀ y = (0) ≥ 0` and `b ⬝ᵥ y = -1 < 0`. -/
private theorem f2Cert_infeasible :
    ¬ ∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧ exACol.mulVec x = ![1, 2] := by
  intro hfeas
  have hF2 := Matrix.exists_nonneg_mulVec_eq_iff exACol (![1, 2] : Fin 2 → ℝ)
  have hAty : ∀ i : Fin 1, 0 ≤ (exACol.transpose.mulVec ![1, -1]) i := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h00 : exACol 0 0 = 1 := by simp [exACol]
    have h10 : exACol 1 0 = 1 := by simp [exACol]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00, h10]
  have hpos := hF2.mp hfeas ![1, -1] hAty
  have hneg : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![1, -1] < 0 := by
    norm_num [dotProduct, Fin.sum_univ_two]
  linarith

/-- FX09 sign freedom: the certificate `y = (1, -1)` is not nonnegative. -/
private theorem f2Cert_signFree : ¬ ∀ j : Fin 2, 0 ≤ (![1, -1] : Fin 2 → ℝ) j := by
  intro hall
  have heq : (![1, -1] : Fin 2 → ℝ) 1 = -1 := by simp
  have h1 := hall 1
  rw [heq] at h1
  norm_num at h1

/-- FX10 counterfactual: `A x = b` holds for the negative `x = -1`. -/
private theorem f2Nonneg_eq : exA1.mulVec ![-1] = ![-1] := by
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  have h00 : exA1 0 0 = 1 := by simp [exA1]
  have hx : (exA1.mulVec ![-1]) 0 = -1 := by
    simp [Matrix.mulVec, dotProduct, h00]
  have hb : (![-1] : Fin 1 → ℝ) 0 = -1 := by simp
  rw [hx, hb]

/-- FX10: still, no `x ≥ 0` solves it, via the certificate `y = (1)`. -/
private theorem f2Nonneg_infeasible :
    ¬ ∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧ exA1.mulVec x = ![-1] := by
  intro hfeas
  have hF2 := Matrix.exists_nonneg_mulVec_eq_iff exA1 (![-1] : Fin 1 → ℝ)
  have hAty : ∀ i : Fin 1, 0 ≤ (exA1.transpose.mulVec ![1]) i := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h00 : exA1 0 0 = 1 := by simp [exA1]
    simp [Matrix.mulVec, dotProduct, h00]
  have hpos := hF2.mp hfeas ![1] hAty
  have hneg : (![-1] : Fin 1 → ℝ) ⬝ᵥ ![1] < 0 := by norm_num [dotProduct]
  linarith

/-- FX11: `A = [[0, 0]]`, `b = (1)` is infeasible via the sign-free
certificate `y = (-1)`, since `Aᵀ y = (0, 0) ≥ 0` and `b ⬝ᵥ y = -1`. -/
private theorem f2Zero_infeasible :
    ¬ ∃ x : Fin 2 → ℝ, (∀ i, 0 ≤ x i) ∧ exAZero.mulVec x = ![1] := by
  intro hfeas
  have hF2 := Matrix.exists_nonneg_mulVec_eq_iff exAZero (![1] : Fin 1 → ℝ)
  have hAty : ∀ i : Fin 2, 0 ≤ (exAZero.transpose.mulVec ![-1]) i := by
    have h00 : exAZero 0 0 = 0 := by simp [exAZero]
    have h01 : exAZero 0 1 = 0 := by simp [exAZero]
    intro i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, h00]
    · simp [Matrix.mulVec, dotProduct, h01]
  have hpos := hF2.mp hfeas ![-1] hAty
  have hneg : (![1] : Fin 1 → ℝ) ⬝ᵥ ![-1] < 0 := by norm_num [dotProduct]
  linarith

/-- FX11 sign freedom: the certificate `y = (-1)` is not nonnegative. -/
private theorem f2Zero_signFree : ¬ ∀ j : Fin 1, 0 ≤ (![-1] : Fin 1 → ℝ) j := by
  intro hall
  have heq : (![-1] : Fin 1 → ℝ) 0 = -1 := by simp
  have h0 := hall 0
  rw [heq] at h0
  norm_num at h0

/-- FX11 rejection: `y = (1)` is not a certificate, since `b ⬝ᵥ y = 1`. -/
private theorem f2Zero_reject : ¬ (![1] : Fin 1 → ℝ) ⬝ᵥ ![1] < 0 := by
  norm_num [dotProduct]

/-- FX12: with no variables (`n = 0`) and `b = (0)`, the empty vector
is feasible. -/
private theorem f2NoVars_zero :
    (∃ x : Fin 0 → ℝ, (∀ i, 0 ≤ x i) ∧
      (0 : Matrix (Fin 1) (Fin 0) ℝ).mulVec x = ![0]) ∧
    (∀ y : Fin 1 → ℝ,
      (∀ i : Fin 0, 0 ≤ ((0 : Matrix (Fin 1) (Fin 0) ℝ).transpose.mulVec y) i) →
      0 ≤ (![0] : Fin 1 → ℝ) ⬝ᵥ y) := by
  have hLHS : ∃ x : Fin 0 → ℝ, (∀ i, 0 ≤ x i) ∧
      (0 : Matrix (Fin 1) (Fin 0) ℝ).mulVec x = ![0] := by
    refine ⟨0, fun i => i.elim0, ?_⟩
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have hAx : ((0 : Matrix (Fin 1) (Fin 0) ℝ).mulVec 0) 0 = 0 := by
      simp [Matrix.mulVec, dotProduct]
    have hb : (![0] : Fin 1 → ℝ) 0 = 0 := by simp
    rw [hAx, hb]
  have hF2 := Matrix.exists_nonneg_mulVec_eq_iff
    (0 : Matrix (Fin 1) (Fin 0) ℝ) (![0] : Fin 1 → ℝ)
  exact ⟨hLHS, hF2.mp hLHS⟩

/-- FX13: with no variables (`n = 0`) and `b = (3)`, infeasible with
F2 certificate `y = (-1)`. -/
private theorem f2NoVars_nonzero :
    ¬ ∃ x : Fin 0 → ℝ, (∀ i, 0 ≤ x i) ∧
      (0 : Matrix (Fin 1) (Fin 0) ℝ).mulVec x = ![3] := by
  intro hfeas
  have hF2 := Matrix.exists_nonneg_mulVec_eq_iff
    (0 : Matrix (Fin 1) (Fin 0) ℝ) (![3] : Fin 1 → ℝ)
  have hAty : ∀ i : Fin 0,
      0 ≤ ((0 : Matrix (Fin 1) (Fin 0) ℝ).transpose.mulVec ![-1]) i :=
    fun i => i.elim0
  have hpos := hF2.mp hfeas ![-1] hAty
  have hneg : (![3] : Fin 1 → ℝ) ⬝ᵥ ![-1] < 0 := by norm_num [dotProduct]
  linarith

/-- FX14: with no constraints (`m = 0`, `n = 1`), `x = (0)` is feasible. -/
private theorem f2NoConstraints_feas :
    (∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧
      (0 : Matrix (Fin 0) (Fin 1) ℝ).mulVec x = ![]) ∧
    (∀ y : Fin 0 → ℝ,
      (∀ i, 0 ≤ ((0 : Matrix (Fin 0) (Fin 1) ℝ).transpose.mulVec y) i) →
      0 ≤ (![] : Fin 0 → ℝ) ⬝ᵥ y) := by
  have hLHS : ∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧
      (0 : Matrix (Fin 0) (Fin 1) ℝ).mulVec x = ![] := by
    refine ⟨![0], ?_, ?_⟩
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp
    · funext j
      exact j.elim0
  have hF2 := Matrix.exists_nonneg_mulVec_eq_iff
    (0 : Matrix (Fin 0) (Fin 1) ℝ) (![] : Fin 0 → ℝ)
  exact ⟨hLHS, hF2.mp hLHS⟩

/-- F3 over the empty generator set in `ℝ`. -/
private theorem f3_empty :
    IsClosed (PointedCone.hull ℝ (↑(∅ : Finset ℝ) : Set ℝ) : Set ℝ) :=
  PointedCone.isClosed_hull_finset (∅ : Finset ℝ)

/-- F3 over a singleton in `ℝ`. -/
private theorem f3_singleton :
    IsClosed (PointedCone.hull ℝ (↑({1} : Finset ℝ) : Set ℝ) : Set ℝ) :=
  PointedCone.isClosed_hull_finset ({1} : Finset ℝ)

/-- F3 over the zero generator in `ℝ`. -/
private theorem f3_zero :
    IsClosed (PointedCone.hull ℝ (↑({0} : Finset ℝ) : Set ℝ) : Set ℝ) :=
  PointedCone.isClosed_hull_finset ({0} : Finset ℝ)

/-- F3 over repeated generators in `ℝ`. -/
private theorem f3_repeated :
    IsClosed (PointedCone.hull ℝ (↑({1, 1} : Finset ℝ) : Set ℝ) : Set ℝ) :=
  PointedCone.isClosed_hull_finset ({1, 1} : Finset ℝ)

/-- F3 over opposing generators in `ℝ`: the hull need not be salient,
and is still closed. -/
private theorem f3_opposing :
    IsClosed (PointedCone.hull ℝ (↑({1, -1} : Finset ℝ) : Set ℝ) : Set ℝ) :=
  PointedCone.isClosed_hull_finset ({1, -1} : Finset ℝ)

/-- F3 over an arbitrary real normed space, with exactly the two required
instances and no finite-dimensionality or `DecidableEq`. -/
private theorem f3_generic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Finset E) :
    IsClosed (PointedCone.hull ℝ (↑S : Set E) : Set E) :=
  PointedCone.isClosed_hull_finset S

end LinearProgrammingDualityTest
