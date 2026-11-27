/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.JacobiThetaTwoProduct

@[expose] public section

open Complex
open scoped Real

example (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ z τ = ∏' n : ℕ,
      ((1 - Complex.exp (2 * π * I * (n + 1) * τ)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ + 2 * π * I * z)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ - 2 * π * I * z))) :=
  jacobiTheta₂_eq_tprod z τ hτ

example : jacobiTheta₂ 0 Complex.I = ∏' n : ℕ,
    ((1 - Complex.exp (2 * π * I * (n + 1) * Complex.I)) *
      (1 + Complex.exp (π * I * (2 * n + 1) * Complex.I + 2 * π * I * 0)) *
      (1 + Complex.exp (π * I * (2 * n + 1) * Complex.I - 2 * π * I * 0))) :=
  jacobiTheta₂_eq_tprod 0 Complex.I (by simp)
