/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.BernoulliEntropy
public import Mathlib.Probability.UniformOn

import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Dynamics.Ergodic.BernoulliShift MathlibExt.Dynamics.Ergodic.KolmogorovSinaiEntropy
open MathlibExt.Dynamics.Ergodic.BernoulliEntropy

namespace MathlibExtTest.Dynamics.Ergodic.BernoulliEntropy

-- The entropy of two independent fair letters is twice the entropy of one.
example : ∑ w : Fin 2 → Bool, Real.negMulLog (∏ k, (fun _ : Bool => (1 / 2 : ℝ)) (w k)) =
    2 * ∑ _b : Bool, Real.negMulLog (1 / 2) :=
  by simpa using sum_negMulLog_prod (a := fun _ : Bool => (1 / 2 : ℝ)) (by norm_num) 2

/-- The fair coin-tossing shift has entropy at least `log 2` (in fact equal to it). -/
theorem log_two_le_ksEntropy_coin :
    ENNReal.ofReal (Real.log 2) ≤
      ksEntropy (Measure.infinitePi fun _ : ℕ => uniformOn (Set.univ : Set Bool)) shift := by
  have h := ofReal_le_ksEntropy_shift (uniformOn (Set.univ : Set Bool))
  have hs : ∀ b : Bool, (uniformOn (Set.univ : Set Bool) {b}).toReal = 1 / 2 := by
    intro b
    rw [uniformOn_univ, Measure.count_singleton]
    norm_num
  simp only [hs, Fintype.sum_bool] at h
  convert h using 2
  rw [Real.negMulLog, one_div, Real.log_inv]
  ring

end MathlibExtTest.Dynamics.Ergodic.BernoulliEntropy
