/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CrossWorldCounterfactual

/-!
# Tests for cross-world non-identification

Observational and interventional values of the constant- and switching-response models, equal
potential-outcome marginals `P(Y_1 = 1) = P(Y_0 = 1) = 1 / 2` in both, and different
cross-world probabilities.
-/

@[expose] public section

namespace Cslib.MachineLearning.CrossWorldTests

open Cslib.MachineLearning.GraphicalModels.CrossWorld

/-- Observational law of the constant-response model: uniform on all four outcomes. -/
example (x y : Bool) : constantResponse.law (none, none) x y = 1 / 4 := by
  cases x <;> cases y <;>
    simp [BinarySCM.law, BinarySCM.solX, BinarySCM.solY, constantResponse,
      Fintype.sum_prod_type]

/-- Observational law of the switching-response model: uniform on all four outcomes. -/
example (x y : Bool) : switchingResponse.law (none, none) x y = 1 / 4 := by
  cases x <;> cases y <;>
    simp [BinarySCM.law, BinarySCM.solX, BinarySCM.solY, switchingResponse,
      Fintype.sum_prod_type]

/-- Intervening `X := true`: `Y` is a fair coin in the switching-response model. -/
example : switchingResponse.law (some true, none) true true = 1 / 2 := by
  simp [BinarySCM.law, BinarySCM.solX, BinarySCM.solY, switchingResponse,
    Fintype.sum_prod_type]
  norm_num

/-- Intervening `Y := false`: `X` stays a fair coin in the constant-response model. -/
example : constantResponse.law (none, some false) true false = 1 / 2 := by
  simp [BinarySCM.law, BinarySCM.solX, BinarySCM.solY, constantResponse,
    Fintype.sum_prod_type]
  norm_num

/-- Potential-outcome marginal `P(Y_1 = 1) = 1 / 2` in the constant-response model. -/
example : (∑ u : Bool × Bool,
    (if constantResponse.fY true u = true then constantResponse.pU u else 0)) = 1 / 2 := by
  simp [constantResponse, Fintype.sum_prod_type]
  norm_num

/-- Potential-outcome marginal `P(Y_0 = 1) = 1 / 2` in the constant-response model. -/
example : (∑ u : Bool × Bool,
    (if constantResponse.fY false u = true then constantResponse.pU u else 0)) = 1 / 2 := by
  simp [constantResponse, Fintype.sum_prod_type]
  norm_num

/-- Potential-outcome marginal `P(Y_1 = 1) = 1 / 2` in the switching-response model. -/
example : (∑ u : Bool × Bool,
    (if switchingResponse.fY true u = true then switchingResponse.pU u else 0)) = 1 / 2 := by
  simp [switchingResponse, Fintype.sum_prod_type]
  norm_num

/-- Potential-outcome marginal `P(Y_0 = 1) = 1 / 2` in the switching-response model. -/
example : (∑ u : Bool × Bool,
    (if switchingResponse.fY false u = true then switchingResponse.pU u else 0)) = 1 / 2 := by
  simp [switchingResponse, Fintype.sum_prod_type]
  norm_num

/-- The cross-world probabilities differ across the two models. -/
example : constantResponse.probY1Y0 ≠ switchingResponse.probY1Y0 := by
  rw [probY1Y0_constantResponse, probY1Y0_switchingResponse]
  norm_num

end Cslib.MachineLearning.CrossWorldTests
