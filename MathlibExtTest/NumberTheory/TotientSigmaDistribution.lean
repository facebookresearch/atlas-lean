/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TotientSigmaDistribution
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.NormNum

/-!
# Tests for the totient of the divisor sum
-/

namespace MathlibExtTest.NumberTheory.TotientSigmaDistribution

open Asymptotics Filter

/-- The constant threshold `f = 1` yields a set of asymptotic density zero. -/
example : (fun x : ℝ => (((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
    (n : ℝ) ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℝ)) =o[atTop]
    (fun x => x) := by
  have hlog₁ := Real.tendsto_log_atTop
  have hlog₄ : Tendsto (fun x => Real.log (Real.log (Real.log (Real.log x)))) atTop atTop :=
    hlog₁.comp (hlog₁.comp (hlog₁.comp hlog₁))
  have hf : (fun _ : ℝ => (1 : ℝ)) =o[atTop]
      (fun x => Real.log (Real.log (Real.log (Real.log x)))) :=
    (isLittleO_const_left_of_ne one_ne_zero).mpr (tendsto_norm_atTop_atTop.comp hlog₄)
  simpa only [div_one] using
    (MetaMathlibExt.card_totient_sigma_ge_div_isBigO (f := fun _ => 1)
      (hpos := fun _ _ => zero_lt_one) (hmono := monotoneOn_const) (hf := hf)).2

/-- At a nonintegral cutoff, the integer `1` is counted when the threshold is attained exactly. -/
example : ((Finset.Icc 1 ⌊(3 / 2 : ℝ)⌋₊).filter fun n : ℕ =>
    (n : ℝ) ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card = 1 := by
  have hfloor : ⌊(3 / 2 : ℝ)⌋₊ = 1 := (Nat.floor_eq_iff (by norm_num)).mpr (by norm_num)
  rw [hfloor, Finset.Icc_self, Finset.filter_eq_self.mpr]
  · exact Finset.card_singleton _
  · intro n hn
    rw [Finset.mem_singleton.mp hn, ArithmeticFunction.sigma_one, Nat.totient_one]

end MathlibExtTest.NumberTheory.TotientSigmaDistribution
