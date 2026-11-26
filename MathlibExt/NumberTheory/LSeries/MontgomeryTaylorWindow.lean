/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Anthropic, PBC (adapted counting conventions and statement types).
Released under the Apache License, Version 2.0, as described in the LICENSE file.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # The Montgomery–Taylor window constant -/

@[expose] public noncomputable section

namespace ComplexZeroCounts

/-- **Montgomery–Taylor window constant.** The constant is
$\sqrt{2}\tan(1/\sqrt{2})/(1+\tan(1/\sqrt{2})/\sqrt{2})$.

Source: Alpöge and Furman, [arXiv:2608.13637](https://arxiv.org/abs/2608.13637). -/
def montgomeryTaylorWindowConstant : ℝ :=
  Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) /
    (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))

end ComplexZeroCounts
