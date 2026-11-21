/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ContinuousBorel
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic.NormNum

noncomputable section

open MathlibExt.Topology.ContinuousBorel

private def two : ℂˣ := Units.mk0 2 (by norm_num)

/-- A nontrivial scalar orbit is normalized by division by its group coordinate. -/
example : levelZero ℂˣ (TopCat.of ℂ)
    (Quotient.mk'' ((fun _ : Fin 1 => two), (6 : ℂ))) = 3 := by
  change two⁻¹ • (6 : ℂ) = 3
  norm_num [two, Units.smul_def, smul_eq_mul]
