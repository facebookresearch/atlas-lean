/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.LinearMediation
public import Mathlib.Tactic.NormNum

/-!
# Tests for linear mediation effects

A contrast other than `0 → 1` (`2 → 5` with `a = 3`, `b = -2`, `c' = 1/2`), surgical solution
values for `do(X = 5)` and for the nested surgery `X := 5`, `do(M = M_2)` with shared noise,
and an interaction counterexample where the natural indirect effect differs from `a b (x₁ - x₀)`.
-/

@[expose] public section

namespace Cslib.MachineLearning.LinearMediationTests

open Cslib.MachineLearning.GraphicalModels.LinearMediation
open Cslib.MachineLearning.GraphicalModels.LinearSEM

/-- Total effect for `a = 3`, `b = -2`, `c' = 1/2`, contrast `2 → 5`: `-33/2`. -/
example (uM uY : ℝ) : (⟨3, -2, 1/2⟩ : MediationModel).totalEffect 2 5 uM uY = -33/2 := by
  rw [MediationModel.totalEffect_eq]
  norm_num

/-- Natural direct effect for the same contrast: `3/2`. -/
example (uM uY : ℝ) :
    (⟨3, -2, 1/2⟩ : MediationModel).naturalDirectEffect 2 5 uM uY = 3/2 := by
  rw [MediationModel.naturalDirectEffect_eq]
  norm_num

/-- Natural indirect effect for the same contrast: `-18`. -/
example (uM uY : ℝ) :
    (⟨3, -2, 1/2⟩ : MediationModel).naturalIndirectEffect 2 5 uM uY = -18 := by
  rw [MediationModel.naturalIndirectEffect_eq]
  norm_num

/-- The surgical solution at `Y` for `do(X = 5)` with noise `![0, 1, 2]`: `-55/2`. -/
example : doSolve (MediationModel.coeffMatrix ⟨3, -2, 1/2⟩) 0 5 ![0, 1, 2] 2 = -55/2 := by
  rw [(MediationModel.doSolve_coeffMatrix ⟨3, -2, 1/2⟩ 5 ![0, 1, 2]).2]
  norm_num [MediationModel.potentialOutcome, MediationModel.outcome, MediationModel.mediator]

/-- Interaction counterexample: with `Y = x + mv + x * mv + uY`, `M = x + uM`, the natural
indirect effect `Y(1, M(1)) - Y(1, M(0))` at zero noise is `2`. -/
example : (let M : ℝ → ℝ → ℝ := (fun x uM => x + uM);
    let Y : ℝ → ℝ → ℝ → ℝ := (fun x mv uY => x + mv + x * mv + uY);
    Y 1 (M 1 0) 0 - Y 1 (M 0 0) 0) = (2 : ℝ) := by
  show (1 + (1 + 0) + 1 * (1 + 0) + 0) - (1 + (0 + 0) + 1 * (0 + 0) + 0) = 2
  norm_num

/-- ...which differs from the no-interaction value `a * b * (x₁ - x₀) = 1`. -/
example : (let M : ℝ → ℝ → ℝ := (fun x uM => x + uM);
    let Y : ℝ → ℝ → ℝ → ℝ := (fun x mv uY => x + mv + x * mv + uY);
    Y 1 (M 1 0) 0 - Y 1 (M 0 0) 0) ≠ (1 : ℝ) * 1 * (1 - 0) := by
  show (1 + (1 + 0) + 1 * (1 + 0) + 0) - (1 + (0 + 0) + 1 * (0 + 0) + 0) ≠ 1 * 1 * (1 - 0)
  norm_num

/-- The nested surgery at `Y` for `do(M = M_2)` with `X := 5` and noise `![7, 1, 2]`: `-19/2`. -/
example :
    doSolve (MediationModel.coeffMatrix ⟨3, -2, 1/2⟩) 1 (MediationModel.mediator ⟨3, -2, 1/2⟩ 2 1)
      (Function.update ![7, 1, 2] 0 5) 2 = -19/2 := by
  rw [show MediationModel.mediator (⟨3, -2, 1/2⟩ : MediationModel) 2 1 =
      MediationModel.mediator ⟨3, -2, 1/2⟩ 2 ((![7, 1, 2] : Fin 3 → ℝ) 1) from by simp]
  rw [MediationModel.doSolve_coeffMatrix_nested]
  norm_num [MediationModel.nestedOutcome, MediationModel.outcome, MediationModel.mediator]

end Cslib.MachineLearning.LinearMediationTests
