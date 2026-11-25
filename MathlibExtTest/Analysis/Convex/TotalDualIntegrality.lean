/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.TotalDualIntegrality

@[expose] public section

open MathlibExt.Analysis.Convex.TotalDualIntegrality

/-! The TDI hypothesis is satisfiable: upper-bound systems `x ≤ b` are TDI, in every dimension. -/

example : IsTDI (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] := isTDI_upperBound _

example (b : Fin 0 → ℝ) : IsTDI (1 : Matrix (Fin 0) (Fin 0) ℝ) b := isTDI_upperBound b
