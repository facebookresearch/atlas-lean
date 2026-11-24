/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.TaylorShiftMul

/-! # Consumers for multiplicativity of the nonarchimedean Taylor shift -/

namespace PowerSeriesTaylorShiftMulTest

open PowerSeries

/-- The exact source statement, with no added hypothesis. -/
public theorem exactSource {L : Type*} [NontriviallyNormedField L] [CompleteSpace L]
    [IsUltrametricDist L] (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M') (a : L) (ha : ‖a‖ < ρ) :
    (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (F * G)
        * ((n + k).choose n : L) * a ^ k)
      = (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F
          * ((n + k).choose n : L) * a ^ k)
        * (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) G
          * ((n + k).choose n : L) * a ^ k) :=
  PowerSeries.taylorShift_mul F G hρ hF hG a ha

/-- Boundary case `a = 0`: the shifted series is the series itself, since
only the `k = 0` term of each coefficient sum survives. -/
public example {L : Type*} [NontriviallyNormedField L] [CompleteSpace L]
    [IsUltrametricDist L] (F : PowerSeries L) :
    PowerSeries.taylorShift (0 : L) F = F := by
  ext n
  rw [PowerSeries.coeff_taylorShift]
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

end PowerSeriesTaylorShiftMulTest
