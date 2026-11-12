/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib









open Filter Topology

namespace StatMech.Probability


theorem pow_negLog_div_le_negLog_div_add_const_of_mul_le_mul_pow
    {a b tail corr : Real} {k height : Nat}
    (ha : 0 < a) (hb : 0 < b) (htail : 0 < tail) (hcorr : 0 < corr)
    (hheight : 0 < height)
    (h : a * tail <= b * corr ^ k) :
    (k : Real) * (-Real.log corr / (height : Real)) <=
      -Real.log tail / (height : Real) +
        (Real.log b - Real.log a) / (height : Real) := by
  have hlog := Real.log_le_log (mul_pos ha htail) h
  rw [Real.log_mul ha.ne' htail.ne',
    Real.log_mul hb.ne' (pow_pos hcorr k).ne', Real.log_pow] at hlog
  have hheightReal : (0 : Real) < height := by exact_mod_cast hheight
  rw [show (k : Real) * (-Real.log corr / (height : Real)) =
      (-((k : Real) * Real.log corr)) / (height : Real) by ring,
    <- add_div, div_le_div_iff_of_pos_right hheightReal]
  linarith




theorem pow_negLogRate_le_negLogRate_of_mul_le_mul_pow
    {tail corr : Nat -> Real} {height : Nat -> Nat}
    {a b tailRate corrRate : Real} {k : Nat}
    (ha : 0 < a) (hb : 0 < b)
    (htail : forall n, 0 < tail n) (hcorr : forall n, 0 < corr n)
    (hheightPos : forall n, 0 < height n)
    (hheight : Tendsto height atTop atTop)
    (hbound : forall n, a * tail n <= b * corr n ^ k)
    (htailRate : Tendsto (fun n =>
      -Real.log (tail n) / (height n : Real)) atTop (nhds tailRate))
    (hcorrRate : Tendsto (fun n =>
      -Real.log (corr n) / (height n : Real)) atTop (nhds corrRate)) :
    (k : Real) * corrRate <= tailRate := by
  have hconst : Tendsto (fun n =>
      (Real.log b - Real.log a) / (height n : Real))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat
      (Real.log b - Real.log a)).comp hheight
  have hleft : Tendsto (fun n =>
      (k : Real) * (-Real.log (corr n) / (height n : Real)))
      atTop (nhds ((k : Real) * corrRate)) :=
    hcorrRate.const_mul (k : Real)
  have hright : Tendsto (fun n =>
      -Real.log (tail n) / (height n : Real) +
        (Real.log b - Real.log a) / (height n : Real))
      atTop (nhds (tailRate + 0)) := htailRate.add hconst
  have hle := le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall fun n =>
      pow_negLog_div_le_negLog_div_add_const_of_mul_le_mul_pow
        ha hb (htail n) (hcorr n) (hheightPos n) (hbound n))
  simpa using hle

end StatMech.Probability
