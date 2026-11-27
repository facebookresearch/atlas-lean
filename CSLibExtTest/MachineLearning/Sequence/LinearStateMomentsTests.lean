/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.Sequence.LinearStateMoments
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Regressions for linear-state moments -/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix ENNReal
open Cslib.MachineLearning.Sequence.LinearStateMoments
open MathlibExt.Probability.Finance.PortfolioVariance (covMatrix)

namespace CSLibExtTest.MachineLearning.LinearStateMoments

private noncomputable def P : Measure (Fin 3) := Measure.uniformOfFinset Finset.univ

private instance : IsProbabilityMeasure P := by
  rw [isProbabilityMeasure_iff, P, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
  exact ENNReal.div_self (by norm_num) (by simp)

private theorem integral_three (f : Fin 3 → ℝ) :
    (∫ ω, f ω ∂P) = (f 0 + f 1 + f 2) / 3 := by
  rw [integral_fintype Integrable.of_finite]
  have h (i : Fin 3) : P.real {i} = 1 / 3 := by
    rw [measureReal_def, P, Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ i),
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
    norm_num
  simp only [h, smul_eq_mul, Fin.sum_univ_three]
  ring

private def r (ω : Fin 3) : ℝ := (ω.val : ℝ) - 1
private def s (ω : Fin 3) : ℝ := r ω ^ 2 + 1

private theorem cov_rs : covariance r s P = 0 := by
  rw [covariance_eq_sub MemLp.of_discrete MemLp.of_discrete]
  simp only [integral_three, Pi.mul_apply]
  norm_num [r, s]

-- The noise values are dependent: the two events below both select the same single atom.
example : ¬ r ⟂ᵢ[P] s := by
  intro h
  have he₁ : r ⁻¹' ({0} : Set ℝ) = {1} := by
    ext ω
    fin_cases ω <;> norm_num [r]
  have he₂ : s ⁻¹' ({1} : Set ℝ) = {1} := by
    ext ω
    fin_cases ω <;> norm_num [r, s]
  have he := h.measure_inter_preimage_eq_mul {0} {1}
    (measurableSet_singleton 0) (measurableSet_singleton 1)
  rw [he₁, he₂, Set.inter_self] at he
  have hs : P ({1} : Set (Fin 3)) = (3 : ℝ≥0∞)⁻¹ := by
    rw [P, Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ _)]
    norm_num
  rw [hs] at he
  have he' := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at he'
  norm_num at he'

private def w (k : ℕ) (ω : Fin 3) (_ : Fin 1) : ℝ :=
  if k = 0 then r ω else if k = 1 then s ω else 0

private theorem w_uncorr (k l : ℕ) (hl : l < k) (i j : Fin 1) :
    covariance (fun ω => w k ω i) (fun ω => w l ω j) P = 0 := by
  by_cases hk : k = 1
  · subst k
    have hl' : l = 0 := by omega
    subst l
    simpa [w, covariance_comm s r] using cov_rs
  · have hk0 : k ≠ 0 := by omega
    simp only [w, ite_eq_right hk0, ite_eq_right hk]
    exact covariance_const_left 0

-- Use A = 2, a deterministic input of 3, a constant initial state of 1, and the two
-- dependent noises above. At the second update the cross term is zero, while the
-- nonzero noise mean and variance both contribute to the result.
example :
    let A : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 2
    let B : Matrix (Fin 1) (Fin 1) ℝ := 1
    let u : ℕ → Fin 1 → ℝ := fun _ _ => 3
    let x := state A B u (fun _ _ => 1) w
    (∫ ω, x 2 ω 0 ∂P) = 44 / 3 ∧
    covariance (fun ω => x 1 ω 0) s P = 0 ∧
    covMatrix P (fun i ω => x 2 ω i) 0 0 = 26 / 9 := by
  let A : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 2
  let B : Matrix (Fin 1) (Fin 1) ℝ := 1
  let u : ℕ → Fin 1 → ℝ := fun _ _ => 3
  let x := state A B u (fun _ _ => 1) w
  have h := mean_covariance_update (P := P) A B u (fun _ _ => 1) w
    (fun _ => memLp_const _) (fun _ _ => MemLp.of_discrete)
    (fun _ _ _ => covariance_const_right 1) w_uncorr 1
  have hx1 (ω : Fin 3) : x 1 ω 0 = 5 + r ω := by
    change (A *ᵥ (fun _ : Fin 1 => (1 : ℝ)) + B *ᵥ u 0 + w 0 ω) 0 = _
    norm_num [A, B, u, w, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  change (∫ ω, x 2 ω 0 ∂P) = 44 / 3 ∧ covariance (fun ω => x 1 ω 0) s P = 0 ∧
    covMatrix P (fun i ω => x 2 ω i) 0 0 = 26 / 9
  refine ⟨?_, ?_, ?_⟩
  · have he := congrFun h.2.1 0
    change (∫ ω, x 2 ω 0 ∂P) =
      (A *ᵥ (fun i => ∫ ω, x 1 ω i ∂P) + B *ᵥ u 1 + fun i => ∫ ω, w 1 ω i ∂P) 0 at he
    rw [he]
    norm_num [A, B, u, w, Matrix.mulVec, dotProduct, Fin.sum_univ_one, integral_three, hx1, r, s]
  · have he := h.2.2.1 0 0
    change covariance (fun ω => x 1 ω 0) (fun ω => w 1 ω 0) P = 0 at he
    have hw1 : (fun ω => w 1 ω 0) = s := by
      funext ω
      simp [w]
    rwa [hw1] at he
  · have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) h.2.2.2
    change covMatrix P (fun i ω => x 2 ω i) 0 0 =
      (A * covMatrix P (fun i ω => x 1 ω i) * Aᵀ + covMatrix P (fun i ω => w 1 ω i)) 0 0 at he
    rw [he]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one,
      covMatrix, Matrix.of_apply]
    rw [covariance_eq_sub MemLp.of_discrete MemLp.of_discrete,
      covariance_eq_sub MemLp.of_discrete MemLp.of_discrete]
    norm_num [A, w, Pi.mul_apply, integral_three, hx1, r, s]

end CSLibExtTest.MachineLearning.LinearStateMoments
