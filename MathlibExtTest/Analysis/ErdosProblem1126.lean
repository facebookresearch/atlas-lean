/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ErdosProblem1126
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability

open MathlibExt.Analysis.ErdosProblem1126Wanted

open MeasureTheory Filter

private noncomputable def spike (x : ℝ) : ℝ := if x = 0 then 1 else 0

private theorem spike_ae_additive :
    ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), spike (p.1 + p.2) = spike p.1 + spike p.2 := by
  have hzero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0} := by
    measurability
  have h : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0 := by
    rw [Measure.ae_prod_iff_ae_ae hmeas]
    filter_upwards [hzero] with x hx
    exact (hzero.and ((measurePreserving_add_left volume x).quasiMeasurePreserving.ae hzero)).mono
      fun _ hy ↦ ⟨hx, hy⟩
  filter_upwards [h] with p hp
  simp [spike, hp.1, hp.2.1, hp.2.2]

-- The exceptional value at zero must actually change in an additive representative.
example : ∃ h : ℝ → ℝ, (∀ x y, h (x + y) = h x + h y) ∧
    (∀ᵐ x ∂volume, spike x = h x) ∧ spike 0 ≠ h 0 := by
  obtain ⟨h, hadd, hae⟩ := conjecture_holds spike spike_ae_additive
  have h0 : h 0 = 0 := by
    have h00 := hadd 0 0
    rw [zero_add] at h00
    linarith
  exact ⟨h, hadd, hae, by simp [spike, h0]⟩
