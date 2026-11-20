/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingAntiperiodicProduct
import Code.FrontierA.QuantumIsingSymbolReduction
import Mathlib.Analysis.SpecialFunctions.Arcosh








open scoped BigOperators

namespace StatMech.FrontierA

noncomputable def quantumIsingSpectralRoot (a : Real) : Real :=
  a + Real.sqrt (a ^ 2 - 1)

theorem quantumIsingSpectralRoot_gt_one {a : Real} (ha : 1 < a) :
    1 < quantumIsingSpectralRoot a := by
  unfold quantumIsingSpectralRoot
  have hs : 0 ≤ Real.sqrt (a ^ 2 - 1) := Real.sqrt_nonneg _
  linarith

theorem quantumIsingSpectralRoot_inv {a : Real} (ha : 1 ≤ a) :
    (quantumIsingSpectralRoot a)⁻¹ = a - Real.sqrt (a ^ 2 - 1) := by
  exact Real.add_sqrt_self_sq_sub_one_inv ha

theorem quantumIsingSpectralRoot_add_inv {a : Real} (ha : 1 ≤ a) :
    (quantumIsingSpectralRoot a + (quantumIsingSpectralRoot a)⁻¹) / 2 = a := by
  rw [quantumIsingSpectralRoot_inv ha]
  unfold quantumIsingSpectralRoot
  ring

@[simp] theorem log_quantumIsingSpectralRoot (a : Real) :
    Real.log (quantumIsingSpectralRoot a) = Real.arcosh a := by
  rfl



theorem sum_log_spectralParameter_sub_cos_antiperiodic
    (n : Nat) (hn : n ≠ 0) (a : Real) (ha : 1 < a) :
    (∑ j ∈ Finset.range n,
      Real.log (a - Real.cos (quantumIsingAntiperiodicAngle n j))) =
      -(n : Real) * Real.log 2 +
        (n : Real) * Real.arcosh a +
        2 * Real.log (1 + (quantumIsingSpectralRoot a)⁻¹ ^ n) := by
  let r := quantumIsingSpectralRoot a
  have hr : 1 < r := quantumIsingSpectralRoot_gt_one ha
  have hrepr : (r + r⁻¹) / 2 = a :=
    quantumIsingSpectralRoot_add_inv ha.le
  have h := sum_log_sub_cos_quantumIsingAntiperiodicAngle n hn r hr
  rw [hrepr] at h
  simpa [r, log_quantumIsingSpectralRoot a] using h


theorem sum_log_quantumIsingTrotterReducedParameter_sub_cos
    (beta h k : Real) (n : Nat) (hn : n ≠ 0)
    (ha : 1 < quantumIsingTrotterReducedParameter beta h n k) :
    (∑ j ∈ Finset.range n,
      Real.log (quantumIsingTrotterReducedParameter beta h n k -
        Real.cos (quantumIsingAntiperiodicAngle n j))) =
      -(n : Real) * Real.log 2 +
        (n : Real) * Real.arcosh
          (quantumIsingTrotterReducedParameter beta h n k) +
        2 * Real.log (1 +
          (quantumIsingSpectralRoot
            (quantumIsingTrotterReducedParameter beta h n k))⁻¹ ^ n) :=
  sum_log_spectralParameter_sub_cos_antiperiodic n hn _ ha

end StatMech.FrontierA
