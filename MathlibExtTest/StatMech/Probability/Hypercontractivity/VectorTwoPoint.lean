/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.VectorTwoPoint

/-!
# Tests for `MathlibExt.Probability.Hypercontractivity.VectorTwoPoint`

* `vtp_vectorTwoPoint` proves `bnt_VectorTwoPoint ρ` for `0 ≤ ρ ≤ 1`; instantiated at `ρ = 1/2`;
* `vtp_hypercontractivity` (Bonami–Beckner, `‖T_ρ f‖₂ ≤ ‖f‖_(1+ρ²)`) at `ρ = 1/2`, `n = 2`, for an
  arbitrary `f` and for the dictator `f ω = if ω 0 then 1 else -1`;
* `vtp_qnorm2_sq` and `vtp_uexp_inner_le` (Cauchy–Schwarz) at a concrete function.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.Hypercontractivity.VectorTwoPoint

open _root_.StatMech.Probability

-- The vector two-point inequality at `ρ = 1/2`.
example : bnt_VectorTwoPoint (1 / 2) := vtp_vectorTwoPoint (by norm_num) (by norm_num)

-- Hypercontractivity at `ρ = 1/2` on `Fin 2 → Bool`, for any `f`.
example (f : (Fin 2 → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp (1 / 2) f) ≤ bnt_qnorm (1 + (1 / 2) ^ 2) f :=
  vtp_hypercontractivity (by norm_num) (by norm_num) 2 f

-- Hypercontractivity for the dictator function `±1` on the first coordinate.
example : bnt_qnorm 2 (bnt_noiseOp (1 / 2) (fun ω : Fin 2 → Bool => if ω 0 then 1 else -1))
    ≤ bnt_qnorm (1 + (1 / 2) ^ 2) (fun ω : Fin 2 → Bool => if ω 0 then 1 else -1) :=
  vtp_hypercontractivity (by norm_num) (by norm_num) 2 _

-- `‖u‖₂² = E u²`, evaluated for the constant `2`: both equal `4`.
example : (bnt_qnorm 2 (fun _ : Fin 1 → Bool => (2 : ℝ))) ^ 2 = 4 := by
  rw [vtp_qnorm2_sq]
  simp [bnt_qnormPow, bnt_uexp]
  norm_num

-- Cauchy–Schwarz for the uniform expectation.
example (u : (Fin 1 → Bool) → ℝ) :
    bnt_uexp (fun ω => u ω * u ω) ≤ bnt_qnorm 2 u * bnt_qnorm 2 u :=
  vtp_uexp_inner_le u u

end MathlibExtTest.StatMech.Probability.Hypercontractivity.VectorTwoPoint
