/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.LucasPolytopicNumberEvenLambertSeries

/-!
# Tests for the even-index Lucas-bracket sum

Check absolute summability and specialize the sum formula to the Mersenne parameters, for
which the first Lambert argument is negative.
-/

namespace MathlibExtTest.NumberTheory.LucasPolytopicNumberEvenLambertSeries

open MetaMathlibExt

example (P : LucasParameters) (hs : 0 < P.s) (hdisc : 0 < P.s ^ 2 + 4 * P.t) :
    Summable (fun n : ℕ => |P.t ^ (n + 1) / lucasBracket P (2 * (n + 1))|) :=
  (hasSum_pow_div_lucasBracket_two_mul P hs hdisc).summable.abs

private def mersenneParameters : LucasParameters where
  s := 3
  t := -2
  s_ne_zero := by norm_num
  t_ne_zero := by norm_num
  bracket_ne_zero := by
    have h (n : ℕ) : lucasBracketAux 3 (-2) n = 2 ^ n - 1 := by
      induction n using Nat.twoStepInduction with
      | zero => norm_num [lucasBracketAux]
      | one => norm_num [lucasBracketAux]
      | more n ih₀ ih₁ =>
        change 3 * lucasBracketAux 3 (-2) (n + 1) + (-2) * lucasBracketAux 3 (-2) n = _
        rw [ih₀, ih₁, pow_succ _ (n + 1), pow_succ _ n]
        ring
    intro n hn
    rw [h]
    exact (sub_pos.mpr (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hn)).ne'

example :
    let L : ℝ → ℝ := fun q => ∑' n : ℕ, q ^ (n + 1) / (1 - q ^ (n + 1))
    HasSum (fun n : ℕ => (-2) ^ (n + 1) / lucasBracket mersenneParameters (2 * (n + 1)))
      (L (-1 / 2) - L (1 / 4)) := by
  intro L
  have hdisc : mersenneParameters.s ^ 2 + 4 * mersenneParameters.t = 1 := by
    norm_num [mersenneParameters]
  have h := hasSum_pow_div_lucasBracket_two_mul mersenneParameters
    (by norm_num [mersenneParameters]) (by rw [hdisc]; norm_num)
  have hd : Real.sqrt (mersenneParameters.s ^ 2 + 4 * mersenneParameters.t) = 1 := by
    rw [hdisc, Real.sqrt_one]
  have hq : ((mersenneParameters.s - 1) / 2) ^ 2 / mersenneParameters.t = -1 / 2 := by
    norm_num [mersenneParameters]
  have hq2 : ((mersenneParameters.s - 1) / 2) ^ 4 / mersenneParameters.t ^ 2 = 1 / 4 := by
    norm_num [mersenneParameters]
  simp only [hd, hq, hq2, one_mul] at h
  have ht : mersenneParameters.t = -2 := rfl
  simpa only [ht, L] using h

end MathlibExtTest.NumberTheory.LucasPolytopicNumberEvenLambertSeries
