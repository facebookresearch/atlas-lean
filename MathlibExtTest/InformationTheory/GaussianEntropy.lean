/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.GaussianEntropy

import Mathlib.Tactic.NormNum

open scoped NNReal Real

/-- Boundary check: the entropy formula instantiates at unit
variance. -/
example : gaussEntropy 1 =
    (1 / 2) * Real.log (2 * π * Real.exp 1 * ((1 : ℝ≥0) : ℝ)) :=
  gaussEntropy_eq (by norm_num)
