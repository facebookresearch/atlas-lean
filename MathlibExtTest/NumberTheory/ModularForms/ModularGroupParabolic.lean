/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.ModularGroupParabolic

open scoped MatrixGroups

/-- `T` itself has trace `2`, so it is conjugate to a power of `T` with `ε = 1`. -/
example : ∃ (ε δ : SL(2, ℤ)) (h : ℤ), (ε = 1 ∨ ε = -1) ∧
    ModularGroup.T = ε * (δ * ModularGroup.T ^ h * δ⁻¹) :=
  ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four ModularGroup.T (by
    simp [Matrix.trace_fin_two, ModularGroup.coe_T])
