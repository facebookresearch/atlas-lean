/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexLiteralCountLaws
import Code.Universality.HexConnEndgame

namespace StatMech.Universality

open Filter Topology
open scoped Topology Real



noncomputable def hexLiteralSAWCount (n : ℕ) : ℝ :=
  hlc_sawCountR 0 0 n


theorem hexLiteralSAWCount_eq (a : ℂ) (h0 : ℤ) (n : ℕ) :
    hexLiteralSAWCount n = hlc_sawCountR a h0 n := by
  exact hlc_sawCountR_rebase a 0 h0 0 n

theorem hexLiteralSAWCount_one_le (n : ℕ) : 1 ≤ hexLiteralSAWCount n :=
  hlc_one_le_sawCountR 0 0 n

theorem hexLiteralSAWCount_submultiplicative :
    Submultiplicative hexLiteralSAWCount :=
  hlc_sawCountR_submultiplicative 0 0




theorem hexLiteral_connective_constant_of_series
    (hdiv : ¬ Summable (fun n => hexLiteralSAWCount n * hexChiE ^ n))
    (hconv : ∀ x, 0 ≤ x → x < hexChiE →
      Summable (fun n => hexLiteralSAWCount n * x ^ n)) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (hexLiteralSAWCount n) ^ ((n : ℝ)⁻¹))
        atTop (𝓝 kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) :=
  hex_connective_constant hexLiteralSAWCount hexLiteralSAWCount_one_le
    hexLiteralSAWCount_submultiplicative hdiv hconv



theorem hlc_connective_constant_of_series (a : ℂ) (h0 : ℤ)
    (hdiv : ¬ Summable (fun n => hlc_sawCountR a h0 n * hexChiE ^ n))
    (hconv : ∀ x, 0 ≤ x → x < hexChiE →
      Summable (fun n => hlc_sawCountR a h0 n * x ^ n)) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (hlc_sawCountR a h0 n) ^ ((n : ℝ)⁻¹))
        atTop (𝓝 kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) :=
  hex_connective_constant (hlc_sawCountR a h0)
    (hlc_one_le_sawCountR a h0) (hlc_sawCountR_submultiplicative a h0)
    hdiv hconv

end StatMech.Universality
