/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.MechanismDesign.TruthfulSchedulingLowerBound

import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace MathlibExtTest.GameTheory.MechanismDesign.TruthfulSchedulingLowerBound

@[expose] public section

open MathlibExt.GameTheory.MechanismDesign.TruthfulScheduling

/-- T1: at factor `3 / 2`, some task count defeats every truthful
two-machine mechanism. -/
theorem t1_no_truthful_threeHalves_approx :
    ∃ m : ℕ, ∀ (A : (Fin 2 → Fin m → ℝ) → Fin m → Fin 2)
      (P : (Fin 2 → Fin m → ℝ) → Fin 2 → ℝ),
      IsTruthful A P → ¬ IsApproximate (3 / 2 : ℝ) A :=
  exists_taskCount_not_isApproximate_of_isTruthful_of_lt_two (by norm_num)

end

end MathlibExtTest.GameTheory.MechanismDesign.TruthfulSchedulingLowerBound
