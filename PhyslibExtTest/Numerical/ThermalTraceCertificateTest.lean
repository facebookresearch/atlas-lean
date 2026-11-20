/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Numerical.ThermalTraceCertificate
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Numerical.ThermalTraceCertificate`

* the exact rational trace `y_j = (9 / 10) ^ j`, `j = 0, …, 10`, is accepted by kernel reduction,
  and four modified traces are rejected: a changed intermediate entry with the terminal value
  kept, a truncated trace that still ends at `(9 / 10) ^ 10`, the doubled trace starting at `2`,
  and a trace with a twelfth entry;
* soundness on the accepted trace, at the intermediate entry `j = 5` and at the terminal entry;
* a body of heat capacity `500` coupled through `G = 5` to a bath at `300` (`τ = 100`), started at
  `350`: the endpoint reconstructed from the accepted trace is the tenth Euler iterate from `350`,
  equals `317.433922005` and lies within `5` of the exact `T(100)`.
-/

@[expose] public section

namespace PhyslibExtTest.Numerical.ThermalTraceCertificate

open _root_.ThermalTraceCertificate _root_.PhysicalErrorBudgets

/-! ## A. Accepted and rejected traces -/

/-- The exact rational trace `y_j = (9 / 10) ^ j`, `j = 0, …, 10`, written out. -/
def thermalTraceFixture : List ℚ :=
  [1, 9 / 10, 81 / 100, 729 / 1000, 6561 / 10000, 59049 / 100000, 531441 / 1000000,
    4782969 / 10000000, 43046721 / 100000000, 387420489 / 1000000000, 3486784401 / 10000000000]

/-- **Accepted nonzero trace.** The exact trace is accepted, by kernel reduction. -/
lemma checkThermalTrace_fixture : checkThermalTrace thermalTraceFixture = true := by
  decide +kernel

/-- **Rejected traces.** Each is rejected: one modified intermediate entry with the plausible
terminal value kept; a truncated trace that skips a step and still ends at `(9 / 10) ^ 10`; all
ten identities from the wrong initial value `2`; and an over-long trace with a twelfth entry. -/
lemma checkThermalTrace_rejects :
    checkThermalTrace [1, 9 / 10, 81 / 100, 729 / 1000, 6561 / 10000, 59050 / 100000,
        531441 / 1000000, 4782969 / 10000000, 43046721 / 100000000, 387420489 / 1000000000,
        3486784401 / 10000000000] = false ∧
      checkThermalTrace [1, 9 / 10, 81 / 100, 729 / 1000, 6561 / 10000, 59049 / 100000,
        531441 / 1000000, 4782969 / 10000000, 43046721 / 100000000,
        3486784401 / 10000000000] = false ∧
      checkThermalTrace (thermalTraceFixture.map (2 * ·)) = false ∧
      checkThermalTrace (thermalTraceFixture ++ [31381059609 / 100000000000]) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## B. Soundness on the accepted trace -/

-- An intermediate entry: `y_5 = (9 / 10) ^ 5` after the cast to the reals.
example : ((thermalTraceFixture.getD 5 0 : ℚ) : ℝ) = (9 / 10 : ℝ) ^ 5 :=
  (checkThermalTrace_sound checkThermalTrace_fixture).2 5 (by norm_num)

-- The terminal entry: `y_10 = (9 / 10) ^ 10`.
example : ((thermalTraceFixture.getD 10 0 : ℚ) : ℝ) = (9 / 10 : ℝ) ^ 10 :=
  checkThermalTrace_terminal checkThermalTrace_fixture

/-! ## C. A body cooling in a fixed bath -/

-- The reconstructed endpoint of the body started at `350` is its tenth Euler iterate of size
-- `τ / 10`.
example : traceEndpoint 300 50 thermalTraceFixture =
    (bathEulerStep 500 5 300 (thermalTimeConstant 500 5 / 10))^[10] 350 := by
  rw [traceEndpoint_eq_iterate (C := 500) (G := 5) (by norm_num) (by norm_num) 300 50
    checkThermalTrace_fixture]
  norm_num

/-- **Physical endpoint.** A body of heat capacity `500` coupled through `G = 5` to a bath at `300`
(`τ = 100`), started at `350` (`Δ = 50`): the accepted trace reconstructs
`300 + 50 (9 / 10) ^ 10 = 317.433922005`, within `5` of the exact `T(100)`. -/
lemma traceEndpoint_fixture :
    traceEndpoint 300 50 thermalTraceFixture = 317433922005 / 1000000000 ∧
      |traceEndpoint 300 50 thermalTraceFixture - bathTrajectory 500 5 300 50 100| ≤ 5 := by
  have hacc := checkThermalTrace_fixture
  have hτ : thermalTimeConstant 500 5 = 100 := by norm_num [thermalTimeConstant]
  have herr := traceEndpoint_error (C := 500) (G := 5) (by norm_num) (by norm_num) 300 50 hacc
  rw [hτ] at herr
  refine ⟨?_, ?_⟩
  · norm_num [traceEndpoint, thermalTraceFixture]
  · calc |traceEndpoint 300 50 thermalTraceFixture - bathTrajectory 500 5 300 50 100|
        ≤ |(50 : ℝ)| / 10 := herr
      _ = 5 := by norm_num

end PhyslibExtTest.Numerical.ThermalTraceCertificate
