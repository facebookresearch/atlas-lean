/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.IsIntegral

/-- Integrality over `ℤ_[2]` in the algebraic closure of `ℚ_[2]` is detected
by the norm. -/
example (x : PadicAlgCl 2) : IsIntegral ℤ_[2] x ↔ ‖x‖ ≤ 1 :=
  PadicAlgCl.isIntegral_padicInt_iff_norm_le_one 2 x
