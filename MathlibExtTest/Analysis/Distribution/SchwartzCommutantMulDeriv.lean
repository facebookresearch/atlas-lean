/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Distribution.SchwartzCommutantMulDeriv

/-! # Tests for the scalar commutant on Schwartz space -/

open scoped SchwartzMap
open MathlibExt.Analysis.Distribution.SchwartzCommutantMulDerivWanted

namespace MathlibExtTest.Analysis.Distribution.SchwartzCommutantMulDeriv

-- Use the actual coordinate multiplier. A single fixed, nonzero value determines the operator.
example (T : 𝓢(ℝ, ℂ) →ₗ[ℂ] 𝓢(ℝ, ℂ))
    (hTM : T.comp (SchwartzMap.smulLeftCLM ℂ Complex.ofReal).toLinearMap =
      (SchwartzMap.smulLeftCLM ℂ Complex.ofReal).toLinearMap.comp T)
    (hTd : T.comp (SchwartzMap.derivCLM ℂ ℂ).toLinearMap =
      (SchwartzMap.derivCLM ℂ ℂ).toLinearMap.comp T)
    (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : f a ≠ 0) (hfix : T f a = f a) :
    T = LinearMap.id := by
  obtain ⟨c, hc⟩ := exists_eq_smul_of_comp_mul_eq_of_comp_deriv_eq T _
    (fun g x ↦ SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal g x) hTM hTd
  have heval : c * f a = 1 * f a := by simpa [hc f] using hfix
  have hscalar := mul_right_cancel₀ ha heval
  ext g
  simp [hc g, hscalar]

end MathlibExtTest.Analysis.Distribution.SchwartzCommutantMulDeriv
