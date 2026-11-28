/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.HausdorffYoungSchwartz
import Mathlib.Tactic.NormNum

/-! # Endpoint and interior tests for the Hausdorff–Young inequality -/

open scoped ENNReal FourierTransform

open MathlibExt.Analysis.Fourier.HausdorffYoungSchwartzWanted

-- The same constant works for every Schwartz function at both endpoints and at p = 4/3.
example {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      ‖(𝓕 f).toLp ⊤‖ ≤ C * ‖f.toLp 1‖ ∧
      ‖(𝓕 f).toLp 2‖ ≤ C * ‖f.toLp 2‖ ∧
      ‖(𝓕 f).toLp 4‖ ≤ C * ‖f.toLp (ENNReal.ofReal (4 / 3))‖ := by
  obtain ⟨C, hC, h⟩ := exists_norm_fourier_toLp_le_norm_toLp_of_holderConjugate (n := n)
  have htwo : ENNReal.HolderConjugate 2 2 := by
    simpa using Real.HolderConjugate.two_two.ennrealOfReal
  have h₄ : Real.HolderConjugate (4 / 3) 4 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hone : 1 ≤ ENNReal.ofReal (4 / 3) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hle : ENNReal.ofReal (4 / 3) ≤ 2 := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  exact ⟨C, hC, fun f => ⟨h 1 ⊤ le_rfl (by norm_num) .one_top f,
    h 2 2 (by norm_num) le_rfl htwo f,
    h _ 4 hone hle (by simpa using h₄.ennrealOfReal) f⟩⟩
