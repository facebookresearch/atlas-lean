/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ChannelCapacity

import Mathlib.Tactic.NormNum

open scoped ENNReal

/-- Boundary check: at crossover `δ = 1 / 2` the output is
independent of the input, so the mutual information is
`log 2 - h (1/2) = 0`; here we only instantiate the formula at a
specific crossover value. -/
example : mutualInfo (bscJoint (1 / 2 : ℝ≥0∞) (by norm_num) uniformFin2) =
    Real.log 2 - binEntropy ((1 / 2 : ℝ≥0∞).toReal) :=
  bsc_mutualInfo_uniform (by norm_num)
