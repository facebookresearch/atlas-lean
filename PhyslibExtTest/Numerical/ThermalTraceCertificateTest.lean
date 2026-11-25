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
  equals `317.433922005` and lies within `5` of the exact `T(100)`;
* the same body started at the bath temperature (`Δ = 0`): read as coefficients,
  `T_j = T_amb + Δ y_j`, the accepted trace gives the endpoint `300`, the tenth Euler iterate from
  `300` and the exact `T(100)`, while the quotient `(T_0 - T_amb) / Δ` is Lean's `0 / 0 = 0`, not
  the trace entry `y_0 = 1`;
* the reduced encoding of the exact trace (143 characters, final denominator `10 ^ 10`) decodes to
  that trace and is accepted by kernel reduction; five inputs are rejected by the decoder (a zero
  denominator, a bad digit, a twelfth token, ten tokens, 301 characters), an intermediate entry
  modified with the terminal value kept decodes and is rejected by the recurrence, and the token
  boundaries (leading zeros, `-0`, the bounds `10 ^ 10`, signs, spaces, exponents) are decided the
  same way;
* every decoding lemma is applied: the positional value of a digit run, an admissible token, the
  reduced encoding as eleven admissible tokens, two rejected inputs that are not such encodings, a
  padded unreduced encoding accepted through the checker, the modified encoding rejected through
  the exact characterization, and soundness of the decoded trace at `j = 5`;
* the decoded reduced encoding read as coefficients, `T_j = T_amb + Δ y_j`: the endpoint of the
  body started at `350` lies within `5` of `T(100)`, and at `Δ = 0` the endpoint is `300`, the
  tenth Euler iterate from `300` and the exact `T(100)`.
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

-- Zero initial excess (`Δ = 0`): the body starts at the bath temperature `300`. Read as
-- coefficients, `T_j = T_amb + Δ y_j`, the accepted trace gives the endpoint `300`, which is the
-- tenth Euler iterate from `300` and, by the error bound with `|Δ| / 10 = 0`, the exact `T(100)`.
-- The quotient `(T_0 - T_amb) / Δ` is Lean's `0 / 0 = 0`, not the trace entry `y_0 = 1`.
example : traceEndpoint 300 0 thermalTraceFixture = 300 ∧
    traceEndpoint 300 0 thermalTraceFixture =
      (bathEulerStep 500 5 300 (thermalTimeConstant 500 5 / 10))^[10] 300 ∧
    traceEndpoint 300 0 thermalTraceFixture = bathTrajectory 500 5 300 0 100 ∧
    ((300 : ℝ) - 300) / 0 ≠ ((thermalTraceFixture.getD 0 0 : ℚ) : ℝ) := by
  have hτ : thermalTimeConstant 500 5 = 100 := by norm_num [thermalTimeConstant]
  have hit := traceEndpoint_eq_iterate (C := 500) (G := 5) (by norm_num) (by norm_num) 300 0
    checkThermalTrace_fixture
  have herr := traceEndpoint_error (C := 500) (G := 5) (by norm_num) (by norm_num) 300 0
    checkThermalTrace_fixture
  rw [add_zero] at hit
  rw [hτ, abs_zero, zero_div] at herr
  refine ⟨by simp [traceEndpoint], hit, sub_eq_zero.mp (abs_nonpos_iff.mp herr), ?_⟩
  norm_num [thermalTraceFixture]

/-! ## D. Encoded traces -/

/-- The reduced encoding of the trace `(9 / 10) ^ j`, `j = 0, …, 10`: every entry in lowest
terms. -/
def reducedTraceEncoding : List Char :=
  ("1/1,9/10,81/100,729/1000,6561/10000,59049/100000,531441/1000000,4782969/10000000," ++
    "43046721/100000000,387420489/1000000000,3486784401/10000000000").toList

/-- The reduced encoding with the sixth entry `59049/100000` changed to `59050/100000`; the
terminal entry is kept. -/
def modifiedTraceEncoding : List Char :=
  ("1/1,9/10,81/100,729/1000,6561/10000,59050/100000,531441/1000000,4782969/10000000," ++
    "43046721/100000000,387420489/1000000000,3486784401/10000000000").toList

/-- **Accepted nonzero encoding.** The reduced encoding has 143 characters and ends with the token
`3486784401/10000000000`, of denominator `10 ^ 10`; it decodes to the trace `(9 / 10) ^ j` and is
accepted, by kernel reduction. -/
lemma reducedTraceEncoding_accepted :
    reducedTraceEncoding.length = 143 ∧
      (splitOnChar ',' reducedTraceEncoding).getLast? = some "3486784401/10000000000".toList ∧
      decodeTrace reducedTraceEncoding =
        some ((List.range 11).map fun j => (9 / 10 : ℚ) ^ j) ∧
      checkEncodedTrace reducedTraceEncoding = true := by
  decide +kernel

/-- **Rejected inputs.** A zero denominator in the first token, a non-digit character in the
second, a twelfth token, the first ten tokens alone, and the reduced encoding padded to 301
characters are each rejected by the decoder, by kernel reduction. -/
lemma decodeTrace_rejects :
    decodeTrace ("1/0".toList ++ reducedTraceEncoding.drop 3) = none ∧
      decodeTrace ("1/1,9/1x".toList ++ reducedTraceEncoding.drop 8) = none ∧
      decodeTrace (reducedTraceEncoding ++ ",0/1".toList) = none ∧
      decodeTrace (reducedTraceEncoding.take 120) = none ∧
      decodeTrace (reducedTraceEncoding ++ List.replicate 158 '0') = none := by
  decide +kernel

/-- **A modified intermediate entry.** The modified encoding decodes, with sixth entry
`59050/100000` and the terminal value `(9 / 10) ^ 10` unchanged, and the recurrence check rejects
it. -/
lemma checkEncodedTrace_modified_rejected :
    (decodeTrace modifiedTraceEncoding).map (fun y => y.getD 5 0) = some (59050 / 100000) ∧
      (decodeTrace modifiedTraceEncoding).map (fun y => y.getD 10 0) =
        some ((9 / 10 : ℚ) ^ 10) ∧
      checkEncodedTrace modifiedTraceEncoding = false := by
  decide +kernel

/-- **Token boundaries.** Leading zeros and `-0` decode to their ordinary values, and the bounds
`|numerator| ≤ 10 ^ 10` and `denominator ≤ 10 ^ 10` are attained; one past either bound, a twelfth
digit, a `+` sign, a space, an exponent, a second `/`, a signed denominator and a sign without
digits are rejected. -/
lemma decodeToken_fixtures :
    decodeToken "007/0010".toList = some (7 / 10) ∧
      decodeToken "-0/1".toList = some 0 ∧
      decodeToken "-10000000000/10000000000".toList = some (-1) ∧
      decodeToken "10000000001/1".toList = none ∧
      decodeToken "1/10000000001".toList = none ∧
      decodeToken "000000000001/1".toList = none ∧
      decodeToken "+1/1".toList = none ∧
      decodeToken "1 /1".toList = none ∧
      decodeToken "1e0/1".toList = none ∧
      decodeToken "1/1/1".toList = none ∧
      decodeToken "1/-1".toList = none ∧
      decodeToken "-/1".toList = none := by
  decide +kernel

-- Bounded decimal decoding: the run `0010` has four digits and the positional value `10`.
example : decodeDecimal "0010".toList = some 10 :=
  decodeDecimal_eq_some_iff.mpr
    ⟨by unfold IsDecimalDigits; simp only [← List.all_eq_true]; decide +kernel, by decide +kernel⟩

-- An admissible token: `-0/1`, with sign `-` and digit runs `0` and `1`, decodes to its value `0`.
example : decodeToken "-0/1".toList = some 0 :=
  decodeToken_eq_some_iff.mpr ⟨⟨true, ['0'], ['1']⟩,
    by unfold TraceToken.Admissible IsDecimalDigits; simp only [← List.all_eq_true]; decide +kernel,
    by decide +kernel, by decide +kernel⟩

-- The reduced encoding is the comma-joined encoding of eleven admissible tokens.
example : ∃ ts : List TraceToken, ts.length = 11 ∧ (∀ t ∈ ts, t.Admissible) ∧
    reducedTraceEncoding = [','].intercalate (ts.map TraceToken.encode) := by
  obtain ⟨-, ts, h11, hts, hs, -⟩ :=
    decodeTrace_eq_some_iff.mp reducedTraceEncoding_accepted.2.2.1
  exact ⟨ts, h11, hts, hs⟩

-- Rejection: the input with a twelfth token and the input with a zero denominator have at most
-- 300 characters, so neither is the comma-joined encoding of eleven admissible tokens.
example : ¬∃ ts : List TraceToken, ts.length = 11 ∧ (∀ t ∈ ts, t.Admissible) ∧
    reducedTraceEncoding ++ ",0/1".toList = [','].intercalate (ts.map TraceToken.encode) :=
  fun hts => decodeTrace_eq_none_iff.mp decodeTrace_rejects.2.2.1 ⟨by decide +kernel, hts⟩

example : ¬∃ ts : List TraceToken, ts.length = 11 ∧ (∀ t ∈ ts, t.Admissible) ∧
    "1/0".toList ++ reducedTraceEncoding.drop 3 =
      [','].intercalate (ts.map TraceToken.encode) :=
  fun hts => decodeTrace_eq_none_iff.mp decodeTrace_rejects.1 ⟨by decide +kernel, hts⟩

-- Binding to the checker: a padded, unreduced encoding of the exact trace decodes to
-- `thermalTraceFixture`, which `checkThermalTrace` accepts, so the encoding is accepted.
example :
    checkEncodedTrace ("0001/01,90/100,081/0100,729/1000,6561/10000,59049/100000," ++
      "531441/1000000,4782969/10000000,43046721/100000000,387420489/1000000000," ++
      "03486784401/10000000000").toList = true :=
  checkEncodedTrace_eq_true_iff.mpr ⟨thermalTraceFixture, by decide +kernel,
    checkThermalTrace_fixture⟩

-- The modified encoding does not decode to the trace `(9 / 10) ^ j`, so it is not accepted.
example : checkEncodedTrace modifiedTraceEncoding ≠ true := fun h =>
  absurd (checkEncodedTrace_eq_true_iff_decodeTrace_eq.mp h) (by decide +kernel)

-- Soundness of the accepted reduced encoding at `j = 5`, after the cast to the reals.
example : ∃ y, decodeTrace reducedTraceEncoding = some y ∧
    ((y.getD 5 0 : ℚ) : ℝ) = (9 / 10 : ℝ) ^ 5 := by
  obtain ⟨y, hy, -, hj⟩ := checkEncodedTrace_sound reducedTraceEncoding_accepted.2.2.2
  exact ⟨y, hy, hj 5 (by norm_num)⟩

-- The decoded reduced encoding is the exact trace of section A.
example : decodeTrace reducedTraceEncoding = some thermalTraceFixture := by decide +kernel

-- Read as coefficients, `T_j = T_amb + Δ y_j`: for the body started at `350` in a bath at `300`
-- (`Δ = 50`), the endpoint reconstructed from the decoded trace lies within `5` of `T(100)`.
example : ∃ y, decodeTrace reducedTraceEncoding = some y ∧
    |traceEndpoint 300 50 y - bathTrajectory 500 5 300 50 100| ≤ 5 := by
  obtain ⟨y, hy, hc⟩ := checkEncodedTrace_eq_true_iff.mp reducedTraceEncoding_accepted.2.2.2
  have hτ : thermalTimeConstant 500 5 = 100 := by norm_num [thermalTimeConstant]
  have herr := traceEndpoint_error (C := 500) (G := 5) (by norm_num) (by norm_num) 300 50 hc
  rw [hτ] at herr
  exact ⟨y, hy, herr.trans (by norm_num)⟩

-- At `Δ = 0`, the body started at the bath temperature, the same decoded coefficients give the
-- endpoint `300`, the tenth Euler iterate from `300` and the exact `T(100)`; no quotient by `Δ`
-- appears.
example : ∃ y, decodeTrace reducedTraceEncoding = some y ∧ traceEndpoint 300 0 y = 300 ∧
    traceEndpoint 300 0 y =
      (bathEulerStep 500 5 300 (thermalTimeConstant 500 5 / 10))^[10] 300 ∧
    traceEndpoint 300 0 y = bathTrajectory 500 5 300 0 100 := by
  obtain ⟨y, hy, hc⟩ := checkEncodedTrace_eq_true_iff.mp reducedTraceEncoding_accepted.2.2.2
  have hτ : thermalTimeConstant 500 5 = 100 := by norm_num [thermalTimeConstant]
  have hit := traceEndpoint_eq_iterate (C := 500) (G := 5) (by norm_num) (by norm_num) 300 0 hc
  have herr := traceEndpoint_error (C := 500) (G := 5) (by norm_num) (by norm_num) 300 0 hc
  rw [add_zero] at hit
  rw [hτ, abs_zero, zero_div] at herr
  exact ⟨y, hy, by simp [traceEndpoint], hit, sub_eq_zero.mp (abs_nonpos_iff.mp herr)⟩

end PhyslibExtTest.Numerical.ThermalTraceCertificate
