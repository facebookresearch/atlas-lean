/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.FactorAnalysis
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Positive degrees of freedom in a nonidentified confirmatory factor model -/

@[expose] public section

open Matrix

namespace MathlibExt.Probability.Statistics.Measurement

/-- **Positive degrees of freedom do not imply identification of a factor model.**
The standardized uncorrelated two-factor model with five indicators and one free loading per
indicator has ten free parameters (five loadings and five error variances) and fifteen entries
on or above the covariance diagonal, giving five degrees of freedom. The first three
indicators load on the first factor and the last two on the second. The two displayed parameter
sets have positive loadings in the allowed positions and positive error variances, but give
the same block-diagonal covariance while differing in the magnitude of the fourth loading.
In particular, even the covariance map restricted to positive loadings and variances is not
injective. -/
theorem positive_dof_factor_model_not_identified :
    let Λ := fun (l : Fin 5 → ℝ) => Matrix.of fun (i : Fin 5) (j : Fin 2) =>
      if j = (if i.val < 3 then 0 else 1) then l i else 0
    let cov := fun (l ψ : Fin 5 → ℝ) => factorModelCov (Λ l) 1 (Matrix.diagonal ψ)
    let lA : Fin 5 → ℝ := ![1, 1, 1, 1, 1]
    let lB : Fin 5 → ℝ := ![1, 1, 1, 2, 1 / 2]
    let ψA : Fin 5 → ℝ := ![1, 1, 1, 4, 1]
    let ψB : Fin 5 → ℝ := ![1, 1, 1, 1, 7 / 4]
    let C : Matrix (Fin 5) (Fin 5) ℝ :=
      !![2, 1, 1, 0, 0; 1, 2, 1, 0, 0; 1, 1, 2, 0, 0; 0, 0, 0, 5, 1; 0, 0, 0, 1, 2]
    let nParams := Fintype.card (Fin 5 ⊕ Fin 5)
    let nEntries := (Finset.univ.filter (fun ij : Fin 5 × Fin 5 => ij.1 ≤ ij.2)).card
    nParams = 10 ∧ nEntries = 15 ∧ nEntries - nParams = 5 ∧
      (∀ i, 0 < lA i ∧ 0 < lB i ∧ 0 < ψA i ∧ 0 < ψB i) ∧
      cov lA ψA = C ∧ cov lB ψB = C ∧ |lA 3| ≠ |lB 3| ∧
      ¬ Set.InjOn (fun p : (Fin 5 → ℝ) × (Fin 5 → ℝ) => cov p.1 p.2)
        {p | ∀ i, 0 < p.1 i ∧ 0 < p.2 i} := by
  intro Λ cov lA lB ψA ψB C nParams nEntries
  have hp (i : Fin 5) : 0 < lA i ∧ 0 < lB i ∧ 0 < ψA i ∧ 0 < ψB i := by
    fin_cases i <;> norm_num [lA, lB, ψA, ψB]
  have hA : cov lA ψA = C := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [cov, factorModelCov, Λ, lA, ψA, C, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.diagonal_apply]
  have hB : cov lB ψB = C := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [cov, factorModelCov, Λ, lB, ψB, C, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.diagonal_apply]
  have hdiff : |lA 3| ≠ |lB 3| := by norm_num [lA, lB]
  refine ⟨by decide, by decide, by decide, hp, hA, hB, hdiff, ?_⟩
  intro hinj
  have hEq : (lA, ψA) = (lB, ψB) := hinj
    (fun i => ⟨(hp i).1, (hp i).2.2.1⟩) (fun i => ⟨(hp i).2.1, (hp i).2.2.2⟩)
    (hA.trans hB.symm)
  exact hdiff (congrArg (fun p : (Fin 5 → ℝ) × (Fin 5 → ℝ) => |p.1 3|) hEq)

end MathlibExt.Probability.Statistics.Measurement
