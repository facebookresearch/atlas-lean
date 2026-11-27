/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.DowlingExponentialGeneratingFunction
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- The Dowling numbers of the group of order `2` start `1, 2, 6, 24, 116`.
example :
    (List.range 5).map (qrDowlingNumber (QRWhitney.whitneySecond 2 1 1)) = [1, 2, 6, 24, 116] := by
  norm_num [List.range_succ, qrDowlingNumber_eq_sum, Finset.sum_range_succ,
    QRWhitney.whitneySecond, QRWhitney.qBrack]

-- The series form of the theorem.
example (x : ℂ) :
    ∑' n : ℕ, qrDowlingNumber (QRWhitney.whitneySecond 2 1 1) n * x ^ n / n.factorial =
      Complex.exp (x + (Complex.exp (2 * x) - 1) / 2) :=
  (hasSum_dowling_egf x).tsum_eq

-- At `x = 0` only the term `n = 0` survives, so the theorem recovers `D_0 = 1`.
example : qrDowlingNumber (QRWhitney.whitneySecond 2 1 1) 0 = 1 := by
  have h0 : HasSum
      (fun n : ℕ => qrDowlingNumber (QRWhitney.whitneySecond 2 1 1) n * (0 : ℂ) ^ n /
        n.factorial)
      (qrDowlingNumber (QRWhitney.whitneySecond 2 1 1) 0) := by
    refine (hasSum_ite_eq 0 (qrDowlingNumber (QRWhitney.whitneySecond 2 1 1) 0)).congr_fun
      fun n => ?_
    rcases n with _ | n <;> simp
  simpa using h0.unique (hasSum_dowling_egf 0)

end MetaMathlibExt
