/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.QuantumIsingSectorProductReduction
import Code.FrontierA.QuantumIsingSymbolAsymptotic
import Mathlib.Topology.UniformSpace.UniformConvergence









open Filter
open scoped Topology

namespace StatMech.FrontierA

noncomputable def quantumIsingScaledReducedParameter
    (beta h : Real) (n : Nat) (k : Real) : Real :=
  (n + 1 : Real) ^ 2 *
    (quantumIsingTrotterReducedParameter beta h (n + 1) k - 1)

noncomputable def quantumIsingScaledReducedLimit
    (beta h k : Real) : Real :=
  beta ^ 2 / 8 * quantumIsingDispersion h k ^ 2

theorem quantumIsingScaledReducedParameter_cosineInterpolation
    (beta h : Real) (n : Nat) (k : Real) :
    quantumIsingScaledReducedParameter beta h n k =
      ((1 + Real.cos k) / 2) *
          quantumIsingScaledReducedParameter beta h n 0 +
        ((1 - Real.cos k) / 2) *
          quantumIsingScaledReducedParameter beta h n Real.pi := by
  unfold quantumIsingScaledReducedParameter
    quantumIsingTrotterReducedParameter
  rw [Real.cos_zero, Real.cos_pi]
  ring

theorem quantumIsingScaledReducedLimit_cosineInterpolation
    (beta h k : Real) :
    quantumIsingScaledReducedLimit beta h k =
      ((1 + Real.cos k) / 2) *
          quantumIsingScaledReducedLimit beta h 0 +
        ((1 - Real.cos k) / 2) *
          quantumIsingScaledReducedLimit beta h Real.pi := by
  unfold quantumIsingScaledReducedLimit quantumIsingDispersion
  rw [Real.sq_sqrt (quantumIsing_radicand_nonneg h k),
    Real.sq_sqrt (quantumIsing_radicand_nonneg h 0),
    Real.sq_sqrt (quantumIsing_radicand_nonneg h Real.pi),
    Real.cos_zero, Real.cos_pi]
  ring



theorem quantumIsingScaledReducedParameter_tendstoUniformly
    (beta h : Real) (hbeta : 0 < beta) :
    TendstoUniformly
      (fun n k ↦ quantumIsingScaledReducedParameter beta h n k)
      (quantumIsingScaledReducedLimit beta h) atTop := by
  have hzero := quantumIsingTrotterReducedParameter_scaled_tendsto
    beta h 0 hbeta
  have hpi := quantumIsingTrotterReducedParameter_scaled_tendsto
    beta h Real.pi hbeta
  change Tendsto (fun n ↦ quantumIsingScaledReducedParameter beta h n 0)
      atTop (nhds (quantumIsingScaledReducedLimit beta h 0)) at hzero
  change Tendsto (fun n ↦ quantumIsingScaledReducedParameter beta h n Real.pi)
      atTop (nhds (quantumIsingScaledReducedLimit beta h Real.pi)) at hpi
  rw [Metric.tendsto_atTop] at hzero hpi
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hepsilonHalf : 0 < epsilon / 2 := by positivity
  obtain ⟨Nzero, hNzero⟩ := hzero (epsilon / 2) hepsilonHalf
  obtain ⟨Npi, hNpi⟩ := hpi (epsilon / 2) hepsilonHalf
  rw [eventually_atTop]
  refine ⟨max Nzero Npi, fun n hn k ↦ ?_⟩
  have hz := hNzero n (le_trans (le_max_left _ _) hn)
  have hp := hNpi n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq] at hz hp ⊢
  let w₀ := (1 + Real.cos k) / 2
  let wπ := (1 - Real.cos k) / 2
  have hw₀ : 0 ≤ w₀ := by
    dsimp only [w₀]
    linarith [Real.neg_one_le_cos k]
  have hwπ : 0 ≤ wπ := by
    dsimp only [wπ]
    linarith [Real.cos_le_one k]
  have hwsum : w₀ + wπ = 1 := by
    dsimp only [w₀, wπ]
    ring
  rw [quantumIsingScaledReducedParameter_cosineInterpolation,
    quantumIsingScaledReducedLimit_cosineInterpolation]
  rw [abs_sub_comm]
  change |w₀ * quantumIsingScaledReducedParameter beta h n 0 +
      wπ * quantumIsingScaledReducedParameter beta h n Real.pi -
      (w₀ * quantumIsingScaledReducedLimit beta h 0 +
        wπ * quantumIsingScaledReducedLimit beta h Real.pi)| < epsilon
  rw [show w₀ * quantumIsingScaledReducedParameter beta h n 0 +
        wπ * quantumIsingScaledReducedParameter beta h n Real.pi -
        (w₀ * quantumIsingScaledReducedLimit beta h 0 +
          wπ * quantumIsingScaledReducedLimit beta h Real.pi) =
      w₀ * (quantumIsingScaledReducedParameter beta h n 0 -
        quantumIsingScaledReducedLimit beta h 0) +
      wπ * (quantumIsingScaledReducedParameter beta h n Real.pi -
        quantumIsingScaledReducedLimit beta h Real.pi) by ring]
  calc
    |w₀ * (quantumIsingScaledReducedParameter beta h n 0 -
          quantumIsingScaledReducedLimit beta h 0) +
        wπ * (quantumIsingScaledReducedParameter beta h n Real.pi -
          quantumIsingScaledReducedLimit beta h Real.pi)| ≤
        w₀ * |quantumIsingScaledReducedParameter beta h n 0 -
          quantumIsingScaledReducedLimit beta h 0| +
        wπ * |quantumIsingScaledReducedParameter beta h n Real.pi -
          quantumIsingScaledReducedLimit beta h Real.pi| := by
      simpa [abs_mul, abs_of_nonneg hw₀, abs_of_nonneg hwπ] using
        abs_add_le
          (w₀ * (quantumIsingScaledReducedParameter beta h n 0 -
            quantumIsingScaledReducedLimit beta h 0))
          (wπ * (quantumIsingScaledReducedParameter beta h n Real.pi -
            quantumIsingScaledReducedLimit beta h Real.pi))
    _ ≤ w₀ * (epsilon / 2) + wπ * (epsilon / 2) := by
      gcongr
    _ = epsilon / 2 := by rw [← add_mul, hwsum, one_mul]
    _ < epsilon := by linarith

end StatMech.FrontierA
