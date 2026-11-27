/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.WordMapTraceRangeKourovka16Problem69
import Mathlib.Tactic.NormNum

/-! # Tests for Mycielski's trace-range question -/

namespace MathlibExtTest.GroupTheory.WordMapTraceRangeKourovka16Problem69

open Matrix MathlibExt.GroupTheory.WordMapTraceRangeKourovka16Problem69Wanted

local notation "G₂" => Matrix.GeneralLinearGroup (Fin 2) ℝ
local notation "M₂" => Matrix (Fin 2) (Fin 2) ℝ

example : ¬ (∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Set.Ici (-2 : ℝ) ⊆ Set.range fun xy : G₂ × G₂ =>
      Matrix.trace (FreeGroup.lift ![xy.1, xy.2] w : M₂)) :=
  gl2TraceRangeContainsRay_refuted

private noncomputable def orientationReversing : G₂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![-3, 0; 0, 1] (by norm_num [det_fin_two_of])

-- The endpoint is attained for the first generator, even on an input of negative determinant.
example : (-2 : ℝ) ∈ Set.range fun xy : G₂ × G₂ =>
    Matrix.trace (FreeGroup.lift ![xy.1, xy.2] (FreeGroup.of (0 : Fin 2)) : M₂) := by
  refine ⟨(orientationReversing, 1), ?_⟩
  change Matrix.trace
    (FreeGroup.lift ![orientationReversing, (1 : G₂)] (FreeGroup.of (0 : Fin 2)) : M₂) = -2
  rw [FreeGroup.lift_apply_of]
  change Matrix.trace !![(-3 : ℝ), 0; 0, 1] = -2
  norm_num [Matrix.trace_fin_two_of]

end MathlibExtTest.GroupTheory.WordMapTraceRangeKourovka16Problem69
